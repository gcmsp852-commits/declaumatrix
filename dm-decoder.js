/**
 * dm-decoder.js — Data Matrix (ECC200) decoder, paired with dm.js encoder
 *
 * 対応仕様:
 *  - ECC200 正方シンボル (10×10 〜 144×144)
 *  - Base256 モード + ASCII モード (0-127 + upper shift)
 *  - Reed-Solomon 誤り訂正 (α^1..α^n 根, 多項式 0x12D)
 *  - Management 32bit + 拡張管理部 (location48 / municipality24 含む) の抽出
 *  - XORマスク（ユーザ暗号化）逆適用
 *  - QR Matrix 画像内の DM サンプリング（QR 4 コーナーからの透視変換）
 *  - 単独 DM 画像からのサンプリング
 *
 * API:
 *  - dmdecode.decodeFromImage(imageData, qrLoc, NQR, opts) — 画像 + QR 検出情報から DM を復号
 *  - dmdecode.decodeFromMatrix(mat) — bool[N][N] → codewords → データ
 *  - dmdecode.extractCodewords(mat) — bool[N][N] → rawCodewordBytes
 *  - dmdecode.rsCorrect(codewords, symbol) — RS 訂正
 *  - dmdecode.parseDataStream(dataCodewords) — (1)-(6) 構造のパース
 *  - dmdecode.applyXorMask(codewords, mask) — XOR マスク逆適用
 *
 * 依存: なし（ただし DM_SYMBOLS は dm.js と同一である必要がある）
 */
(function(global) {
  'use strict';

  // ===== DM シンボル表 (dm.js と同一) =====
  const DM_SYMBOLS = [
    { size:10, data:3,    ecc:5,   blocks:1, regions:[1,1], mapping:8   },
    { size:12, data:5,    ecc:7,   blocks:1, regions:[1,1], mapping:10  },
    { size:14, data:8,    ecc:10,  blocks:1, regions:[1,1], mapping:12  },
    { size:16, data:12,   ecc:12,  blocks:1, regions:[1,1], mapping:14  },
    { size:18, data:18,   ecc:14,  blocks:1, regions:[1,1], mapping:16  },
    { size:20, data:22,   ecc:18,  blocks:1, regions:[1,1], mapping:18  },
    { size:22, data:30,   ecc:20,  blocks:1, regions:[1,1], mapping:20  },
    { size:24, data:36,   ecc:24,  blocks:1, regions:[1,1], mapping:22  },
    { size:26, data:44,   ecc:28,  blocks:1, regions:[1,1], mapping:24  },
    { size:32, data:62,   ecc:36,  blocks:1, regions:[2,2], mapping:28  },
    { size:36, data:86,   ecc:42,  blocks:1, regions:[2,2], mapping:32  },
    { size:40, data:114,  ecc:48,  blocks:1, regions:[2,2], mapping:36  },
    { size:44, data:144,  ecc:56,  blocks:1, regions:[2,2], mapping:40  },
    { size:48, data:174,  ecc:68,  blocks:1, regions:[2,2], mapping:44  },
    { size:52, data:204,  ecc:84,  blocks:2, regions:[2,2], mapping:48  },
    { size:64, data:280,  ecc:112, blocks:2, regions:[4,4], mapping:56  },
    { size:72, data:368,  ecc:144, blocks:4, regions:[4,4], mapping:64  },
    { size:80, data:456,  ecc:192, blocks:4, regions:[4,4], mapping:72  },
    { size:88, data:576,  ecc:224, blocks:4, regions:[4,4], mapping:80  },
    { size:96, data:696,  ecc:272, blocks:4, regions:[4,4], mapping:88  },
    { size:104,data:816,  ecc:336, blocks:6, regions:[4,4], mapping:96  },
    { size:120,data:1050, ecc:408, blocks:6, regions:[6,6], mapping:108 },
    { size:132,data:1304, ecc:496, blocks:8, regions:[6,6], mapping:120 },
    { size:144,data:1558, ecc:620, blocks:10,regions:[6,6], mapping:132 }
  ];

  function getSymbolBySize(size) {
    for (const s of DM_SYMBOLS) if (s.size === size) return s;
    return null;
  }

  // ===== GF(256) — dm.js と同じ多項式 0x12D =====
  const DM_PRIM = 0x12D;
  const gfExp = new Uint8Array(512);
  const gfLog = new Uint8Array(256);
  (function initGF() {
    let x = 1;
    for (let i = 0; i < 255; i++) {
      gfExp[i] = x;
      gfLog[x] = i;
      x <<= 1;
      if (x & 0x100) x ^= DM_PRIM;
    }
    for (let i = 255; i < 512; i++) gfExp[i] = gfExp[i - 255];
  })();
  function gfMul(a, b) { return (!a || !b) ? 0 : gfExp[gfLog[a] + gfLog[b]]; }
  function gfDiv(a, b) {
    if (!a) return 0;
    if (!b) throw new Error('division by zero');
    return gfExp[(gfLog[a] + 255 - gfLog[b]) % 255];
  }
  function gfPow(a, p) {
    if (!a) return 0;
    let q = (gfLog[a] * p) % 255;
    if (q < 0) q += 255;
    return gfExp[q];
  }
  function gfInv(a) { return gfExp[(255 - gfLog[a]) % 255]; }
  function gfPolyEval(poly, x) {
    let y = poly[0];
    for (let i = 1; i < poly.length; i++) y = gfMul(y, x) ^ poly[i];
    return y;
  }
  function gfPolyMul(a, b) {
    const res = new Array(a.length + b.length - 1).fill(0);
    for (let i = 0; i < a.length; i++) {
      if (!a[i]) continue;
      for (let j = 0; j < b.length; j++) {
        res[i + j] ^= gfMul(a[i], b[j]);
      }
    }
    return res;
  }
  function gfPolyAdd(a, b) {
    const la = a.length, lb = b.length;
    const len = Math.max(la, lb);
    const res = new Array(len).fill(0);
    for (let i = 0; i < la; i++) res[len - la + i] = a[i];
    for (let i = 0; i < lb; i++) res[len - lb + i] ^= b[i];
    return res;
  }

  // ===== Reed-Solomon 復号 =====
  // ISO/IEC 16022 Annex E: g(x) = ∏_{i=1}^{degree} (x - α^i) → 根は α^1..α^n
  // syndrome S_j = r(α^(j+1)), j=0..n-1
  function rsDecode(msgIn, eccLen) {
    const msg = msgIn.slice(0);
    const synd = new Array(eccLen).fill(0);
    let hasError = false;
    for (let j = 0; j < eccLen; j++) {
      synd[j] = gfPolyEval(msg, gfExp[j + 1]); // α^(j+1)
      if (synd[j]) hasError = true;
    }
    if (!hasError) return { codewords: msg, errors: 0 };
    // Berlekamp-Massey: 誤り位置多項式
    let sigma = [1];
    let prev = [1];
    let L = 0;
    let b = 1;
    let m = 1;
    for (let n = 0; n < eccLen; n++) {
      // 離散(discrepancy)
      let delta = synd[n];
      for (let i = 1; i <= L; i++) {
        delta ^= gfMul(sigma[sigma.length - 1 - i], synd[n - i]);
      }
      if (delta === 0) {
        m++;
      } else if (2 * L <= n) {
        const tmp = sigma.slice();
        // sigma = sigma - (delta/b) x^m * prev
        const factor = gfDiv(delta, b);
        const shift = new Array(m).fill(0);
        const scaled = prev.map(c => gfMul(c, factor));
        const sub = scaled.concat(shift);
        sigma = gfPolyAdd(sigma, sub);
        L = n + 1 - L;
        prev = tmp;
        b = delta;
        m = 1;
      } else {
        const factor = gfDiv(delta, b);
        const shift = new Array(m).fill(0);
        const scaled = prev.map(c => gfMul(c, factor));
        const sub = scaled.concat(shift);
        sigma = gfPolyAdd(sigma, sub);
        m++;
      }
    }
    // 誤り位置: Chien 探索で sigma(α^-i)=0 となる i を探す
    const errPositions = [];
    for (let i = 0; i < msg.length; i++) {
      const xInv = gfExp[(255 - i) % 255];
      if (gfPolyEval(sigma, xInv) === 0) errPositions.push(i);
    }
    if (errPositions.length !== L) {
      throw new Error('RS: 誤り位置数が不一致 (L=' + L + ', found=' + errPositions.length + ')');
    }
    // 誤り値: Forney アルゴリズム
    // omega(x) = S(x) * sigma(x) mod x^n
    const S = synd.slice().reverse(); // 多項式形式
    const prod = gfPolyMul(sigma, S);
    const omega = prod.slice(Math.max(0, prod.length - eccLen));
    // sigma'(x): 奇数項のみ (GF(2^m) 特有)
    const sigmaPrime = [];
    for (let i = sigma.length - 2; i >= 0; i -= 2) {
      sigmaPrime.unshift(sigma[i]);
      sigmaPrime.unshift(0);
    }
    sigmaPrime.pop(); // 揃える
    // 各誤り位置で誤り値計算
    for (const pos of errPositions) {
      const xInv = gfExp[(255 - pos) % 255];
      const x = gfExp[pos % 255];
      const num = gfPolyEval(omega, xInv);
      // sigma'(x) (reversed ordering → 手製)
      let sp = 0;
      for (let i = 1; i < sigma.length; i += 2) {
        // sigma の先頭が最高次 → 係数の次数は sigma.length-1-i
        sp ^= gfMul(sigma[sigma.length - 1 - i], gfPow(xInv, i - 1));
      }
      if (sp === 0) throw new Error('RS: sigma prime が 0');
      const errVal = gfMul(num, gfInv(sp));
      msg[msg.length - 1 - pos] ^= errVal;
    }
    // 検証
    for (let j = 0; j < eccLen; j++) {
      if (gfPolyEval(msg, gfExp[j + 1]) !== 0) {
        throw new Error('RS: 訂正後もシンドロームが残る');
      }
    }
    return { codewords: msg, errors: errPositions.length };
  }

  // ===== Utah placement — 逆方向 =====
  // dm.js の dmBuildMatrix を「書込み」→「読取り」に変更したもの。
  // bool[N][N] の mapping array と、読み取るべき charIdx を受け、
  // codewords[charIdx] にビットを復元する。

  // 「未定」を表す値: -1。事前に mapping 配列を全 -1 で初期化しておき、
  // (dm.js と同じく) 配置順でセルを訪問しながら、実際のセル値(0/1)は
  // reader 関数で bool 行列から取得する。

  function extractCodewordsFromMapping(mapping) {
    const nrow = mapping.length;
    const ncol = mapping[0].length;
    // 訪問済フラグ (dm.js の array[r][c] < 0 判定と同じ役割)
    const visited = [];
    for (let r = 0; r < nrow; r++) visited.push(new Uint8Array(ncol));

    const codewords = [];

    function readModule(row, col) {
      let r = row, c = col;
      if (r < 0) { r += nrow; c += 4 - ((nrow + 4) % 8); }
      if (c < 0) { c += ncol; r += 4 - ((ncol + 4) % 8); }
      if (r >= nrow || c >= ncol) return 0;
      visited[r][c] = 1;
      return mapping[r][c] ? 1 : 0;
    }

    function readUtah(row, col) {
      let byte = 0;
      for (let i = 0; i < 8; i++) {
        let dr, dc;
        switch (i) {
          case 0: dr = row - 2; dc = col - 2; break;
          case 1: dr = row - 2; dc = col - 1; break;
          case 2: dr = row - 1; dc = col - 2; break;
          case 3: dr = row - 1; dc = col - 1; break;
          case 4: dr = row - 1; dc = col    ; break;
          case 5: dr = row    ; dc = col - 2; break;
          case 6: dr = row    ; dc = col - 1; break;
          case 7: dr = row    ; dc = col    ; break;
        }
        const bit = readModule(dr, dc);
        byte = (byte << 1) | bit;
      }
      return byte;
    }

    function readCorner1() {
      let b = 0;
      const pos = [[nrow-1,0],[nrow-1,1],[nrow-1,2],[0,ncol-2],[0,ncol-1],[1,ncol-1],[2,ncol-1],[3,ncol-1]];
      for (const [r,c] of pos) {
        visited[r][c] = 1;
        b = (b << 1) | (mapping[r][c] ? 1 : 0);
      }
      return b;
    }
    function readCorner2() {
      let b = 0;
      const pos = [[nrow-3,0],[nrow-2,0],[nrow-1,0],[0,ncol-4],[0,ncol-3],[0,ncol-2],[0,ncol-1],[1,ncol-1]];
      for (const [r,c] of pos) {
        visited[r][c] = 1;
        b = (b << 1) | (mapping[r][c] ? 1 : 0);
      }
      return b;
    }
    function readCorner3() {
      let b = 0;
      const pos = [[nrow-3,0],[nrow-2,0],[nrow-1,0],[0,ncol-2],[0,ncol-1],[1,ncol-1],[2,ncol-1],[3,ncol-1]];
      for (const [r,c] of pos) {
        visited[r][c] = 1;
        b = (b << 1) | (mapping[r][c] ? 1 : 0);
      }
      return b;
    }
    function readCorner4() {
      let b = 0;
      const pos = [[nrow-1,0],[nrow-1,ncol-1],[0,ncol-3],[0,ncol-2],[0,ncol-1],[1,ncol-3],[1,ncol-2],[1,ncol-1]];
      for (const [r,c] of pos) {
        visited[r][c] = 1;
        b = (b << 1) | (mapping[r][c] ? 1 : 0);
      }
      return b;
    }

    // dm.js dmBuildMatrix と同じ走査順序
    let row = 4;
    let col = 0;
    do {
      if (row === nrow && col === 0) {
        codewords.push(readCorner1());
      } else if (row === nrow - 2 && col === 0 && ncol % 4 !== 0) {
        codewords.push(readCorner2());
      } else if (row === nrow - 2 && col === 0 && ncol % 8 === 4) {
        codewords.push(readCorner3());
      } else if (row === nrow + 4 && col === 2 && ncol % 8 === 0) {
        codewords.push(readCorner4());
      }
      do {
        if (row < nrow && col >= 0 && !visited[row][col]) {
          codewords.push(readUtah(row, col));
        }
        row -= 2; col += 2;
      } while (row >= 0 && col < ncol);
      row += 1; col += 3;
      do {
        if (row >= 0 && col < ncol && !visited[row][col]) {
          codewords.push(readUtah(row, col));
        }
        row += 2; col -= 2;
      } while (row < nrow && col >= 0);
      row += 3; col += 1;
    } while (row < nrow || col < ncol);

    return codewords;
  }

  // ===== データ領域抽出: 最終シンボル (L字 + クロック + データ) →
  //        mapping 配列 (regions 分割を除いた純データ領域) =====
  function extractMappingFromCells(cells, symbol) {
    const { size, regions, mapping: mappingSize } = symbol;
    const [rRows, rCols] = regions;
    const regionDataRows = mappingSize / rRows;
    const regionDataCols = mappingSize / rCols;

    const mapping = [];
    for (let r = 0; r < mappingSize; r++) mapping.push(new Array(mappingSize).fill(false));

    for (let ri = 0; ri < rRows; ri++) {
      for (let ci = 0; ci < rCols; ci++) {
        const r0 = ri * (regionDataRows + 2);
        const c0 = ci * (regionDataCols + 2);
        for (let dr = 0; dr < regionDataRows; dr++) {
          for (let dc = 0; dc < regionDataCols; dc++) {
            const mr = ri * regionDataRows + dr;
            const mc = ci * regionDataCols + dc;
            mapping[mr][mc] = !!cells[r0 + 1 + dr][c0 + 1 + dc];
          }
        }
      }
    }
    return mapping;
  }

  // ===== ECC ブロック逆インターリーブ =====
  // dm.js buildFinalCodewords の逆。
  // 入力: finalCw (data+ECC インターリーブ後)
  // 出力: { dataCw (長さ dataCap, 元順序), blockCount, correctedCount }
  function deinterleaveAndCorrect(finalCw, symbol) {
    const { data: dataCap, ecc: eccCap, blocks } = symbol;
    const eccPerBlock = eccCap / blocks;
    const dataBlocks = [];
    const eccBlocks = [];
    for (let b = 0; b < blocks; b++) {
      dataBlocks.push([]);
      eccBlocks.push([]);
    }
    if (blocks === 1) {
      for (let i = 0; i < dataCap; i++) dataBlocks[0].push(finalCw[i] || 0);
      for (let i = 0; i < eccPerBlock; i++) eccBlocks[0].push(finalCw[dataCap + i] || 0);
    } else {
      // データ部: i を 0..maxLen で、ブロック b を 0..blocks で interleave
      // ブロック b のデータ長: Math.ceil((dataCap - b) / blocks) (実際には dataCap を blocks で割ったもの)
      const lens = [];
      for (let b = 0; b < blocks; b++) {
        let n = 0;
        for (let i = b; i < dataCap; i += blocks) n++;
        lens.push(n);
      }
      const maxLen = Math.max(...lens);
      let ptr = 0;
      for (let i = 0; i < maxLen; i++) {
        for (let b = 0; b < blocks; b++) {
          if (i < lens[b]) {
            dataBlocks[b].push(finalCw[ptr++] || 0);
          }
        }
      }
      for (let i = 0; i < eccPerBlock; i++) {
        for (let b = 0; b < blocks; b++) {
          eccBlocks[b].push(finalCw[ptr++] || 0);
        }
      }
    }
    // 各ブロックを RS 訂正
    let totalErrors = 0;
    const correctedDataBlocks = [];
    for (let b = 0; b < blocks; b++) {
      const combined = dataBlocks[b].concat(eccBlocks[b]);
      try {
        const res = rsDecode(combined, eccPerBlock);
        totalErrors += res.errors;
        correctedDataBlocks.push(res.codewords.slice(0, dataBlocks[b].length));
      } catch (e) {
        // 訂正失敗 → 元データそのまま使う (ベストエフォート)
        correctedDataBlocks.push(dataBlocks[b]);
      }
    }
    // 元順序に戻す: dataCw[i % blocks][i / blocks]
    const dataCw = new Array(dataCap).fill(0);
    for (let b = 0; b < blocks; b++) {
      let idx = b;
      for (let j = 0; j < correctedDataBlocks[b].length; j++) {
        if (idx < dataCap) dataCw[idx] = correctedDataBlocks[b][j];
        idx += blocks;
      }
    }
    return { dataCw, errors: totalErrors };
  }

  // ===== XOR マスク逆適用 =====
  function applyXorMask(finalCw, mask) {
    if (!mask || mask.length === 0) return finalCw.slice();
    const out = new Array(finalCw.length);
    for (let i = 0; i < finalCw.length; i++) out[i] = finalCw[i] ^ mask[i % mask.length];
    return out;
  }

  // ===== Base256 復号 (dm.js encodeBase256 の逆) =====
  function b256Unpseudo(byte, pos) {
    const pr = (149 * pos) % 255 + 1;
    let t = byte - pr;
    while (t < 0) t += 256;
    return t & 0xFF;
  }

  // dataCodewords[startIdx] === 231 (latch) を前提
  // 返り値: { bytes: Uint8Array, nextIdx: 消費後の位置 }
  function decodeBase256(dataCodewords, startIdx) {
    if (dataCodewords[startIdx] !== 231) return null;
    let pos = startIdx + 1; // 1-indexed の意味は「ストリーム先頭からの位置」
    // length field (1 or 2 bytes)
    // pos は 1-indexed で out.length+1 に一致
    let len;
    const lenByte = b256Unpseudo(dataCodewords[pos], pos + 1);
    if (lenByte === 0) {
      // 可変長: シンボル終端まで全部データ
      // 今回の encoder では使わないが規格準拠で実装
      len = -1;
    } else if (lenByte <= 249) {
      len = lenByte;
      pos += 1;
    } else {
      const lenByte2 = b256Unpseudo(dataCodewords[pos + 1], pos + 2);
      len = (lenByte - 249) * 250 + lenByte2;
      pos += 2;
    }
    // data bytes
    const bytes = [];
    if (len < 0) {
      // 終端まで
      while (pos < dataCodewords.length) {
        bytes.push(b256Unpseudo(dataCodewords[pos], pos + 1));
        pos++;
      }
    } else {
      for (let i = 0; i < len; i++) {
        if (pos >= dataCodewords.length) break;
        bytes.push(b256Unpseudo(dataCodewords[pos], pos + 1));
        pos++;
      }
    }
    return { bytes: new Uint8Array(bytes), nextIdx: pos };
  }

  // ASCII モード復号 (簡易版: 0-127 のみ + upper shift + PAD)
  function decodeASCIISegment(dataCodewords, startIdx, endIdx) {
    const bytes = [];
    let i = startIdx;
    while (i < endIdx) {
      const c = dataCodewords[i];
      if (c >= 1 && c <= 128) {
        bytes.push(c - 1);
        i++;
      } else if (c === 235 && i + 1 < endIdx) {
        bytes.push(dataCodewords[i + 1] - 1 + 128);
        i += 2;
      } else if (c === 129) {
        // PAD (あるいは区切り)
        break;
      } else {
        // 未対応エンコーディング or noise → skip
        i++;
      }
    }
    return { bytes: new Uint8Array(bytes), nextIdx: i };
  }

  // UTF-8 デコード
  function bytesToString(bytes) {
    try {
      if (typeof TextDecoder !== 'undefined') {
        return new TextDecoder('utf-8', { fatal: false }).decode(bytes);
      }
    } catch (e) {}
    let s = '';
    for (let i = 0; i < bytes.length; i++) s += String.fromCharCode(bytes[i]);
    return s;
  }

  // ===== コード語ストリームパース (構造(1)-(6)) =====
  // (1) 通常データ (Base256 / ASCII)
  // (2) 129 (区切り)
  // (3) 管理部 32bit (4 bytes)
  // (4) 拡張管理部 (任意長・連続バイト)
  // (5) 129 (区切り)
  // (6) 埋め草 (129 + pseudo-random)
  //
  // パッド判定: pos (1-indexed) において R = ((149*pos)%253)+1, pad = 129+R (>254 なら -254)
  // 実際のパッド第 1 バイトは 129 (そのまま), 第 2 バイト以降は上記式。
  // ただし pos = out.length+1 で、out.length は既に「最初の 129」を含む位置なので
  // padStartPos (1-indexed) の 2 番目以降で上式が成立。
  function isExpectedPadByte(byte, onePosIndex) {
    // onePosIndex: 1-indexed の位置
    const R = ((149 * onePosIndex) % 253) + 1;
    let pad = 129 + R;
    if (pad > 254) pad -= 254;
    return (byte & 0xFF) === (pad & 0xFF);
  }

  function parseDataStream(dataCodewords) {
    // (1) 通常データ: ASCII モードなら直接, Base256 なら 231 latch から
    let i = 0;
    let dataBytes = new Uint8Array(0);
    let dataEncoding = 'none';
    if (dataCodewords[0] === 231) {
      const r = decodeBase256(dataCodewords, 0);
      if (r) {
        dataBytes = r.bytes;
        i = r.nextIdx;
        dataEncoding = 'Base256';
      }
    } else if (dataCodewords[0] !== 129 && dataCodewords[0] !== undefined) {
      // ASCII と仮定して、最初の 129 までを復号
      // ただし ASCII モードでも構造体は同じ
      // 最初の 129 の位置を探す (pseudo-random の pad とは衝突しない最初の 129)
      let end = dataCodewords.length;
      for (let k = 0; k < dataCodewords.length; k++) {
        if (dataCodewords[k] === 129) { end = k; break; }
      }
      const r = decodeASCIISegment(dataCodewords, 0, end);
      dataBytes = r.bytes;
      i = end;
      dataEncoding = 'ASCII';
    }

    // (2) 最初の 129 をスキップ
    let firstDelim = -1;
    if (i < dataCodewords.length && dataCodewords[i] === 129) {
      firstDelim = i;
      i++;
    } else {
      // 129 を探す (Base256 復号の終端調整用)
      for (let k = i; k < dataCodewords.length; k++) {
        if (dataCodewords[k] === 129) { firstDelim = k; i = k + 1; break; }
      }
    }

    // (3) 管理部 32bit (4 bytes)
    let mgmt32 = null;
    if (i + 3 < dataCodewords.length) {
      mgmt32 = ((dataCodewords[i] << 24) |
                (dataCodewords[i+1] << 16) |
                (dataCodewords[i+2] << 8) |
                dataCodewords[i+3]) >>> 0;
      i += 4;
    }

    // (4)(5) 第 2 の 129 (擬似ランダム化されていないリテラル 129) を探す。
    //   padStartPos より前にある 129 が区切り (5)。
    //   padStartPos 以降の 129 は pad 第 1 バイト (リテラル) のケースがある。
    // ここでは単純に、次の 129 を探し、その直後から pseudo-random PAD 列が始まるかを検証する。
    let secondDelim = -1;
    for (let k = i; k < dataCodewords.length; k++) {
      if (dataCodewords[k] !== 129) continue;
      // 次のバイトから pseudo-random pad になるか検証
      // pad の第 2 バイト以降: pos=k+2 から isExpectedPadByte
      let valid = true;
      let checked = 0;
      for (let p = k + 1; p < dataCodewords.length && checked < 3; p++, checked++) {
        const pos = p + 1; // 1-indexed
        if (!isExpectedPadByte(dataCodewords[p], pos)) { valid = false; break; }
      }
      if (valid || k === dataCodewords.length - 1) {
        secondDelim = k;
        break;
      }
    }

    const extStart = i;
    const extEnd = (secondDelim >= 0) ? secondDelim : dataCodewords.length;
    const extBytes = new Uint8Array(dataCodewords.slice(extStart, extEnd));

    return {
      data: bytesToString(dataBytes),
      dataBytes,
      dataEncoding,
      managementCode32: mgmt32,
      extBytes,
      firstDelimIndex: firstDelim,
      secondDelimIndex: secondDelim
    };
  }

  // ===== 拡張管理部パース (index.html / jsQR.js と互換) =====
  // 管理ビットのフラグに応じて ext バイト列を順番に切り出す
  // フラグ定義 (jsQR.js / index.html に準拠):
  //   bit 0x0200: creationDateTime 32bit
  //   bit 0x0100: expiry 32bit
  //   bit 0x0080: readerId 32bit
  //   bit 0x0040: managementExt 32bit
  //   bit 0x0020: location 48bit (24+24)
  //   bit 0x0010: municipality 24bit
  //
  // 管理32bit の下位 16bit にこれらフラグが入る（上位 16bit はデータ）。
  // 詳細は index.html parseStandardMgmt 参照 (正確な位置は HTML に委譲する)。
  function parseExtBlocks(extBytes, mgmt32) {
    const out = {
      creationDateTimeExt32: null,
      expiryExt32: null,
      readerIdExt32: null,
      managementExt32: null,
      locationLatExt24: null,
      locationLonExt24: null,
      municipalityExt24: null
    };
    if (mgmt32 === null || mgmt32 === undefined) return out;

    // フラグ(bit mask)。QR Matrix Generator の管理部フラグと整合するよう、
    // とりあえず下位 16bit をフラグ領域として扱う。
    const flags = mgmt32 & 0xFFFF;

    let p = 0;
    const readU32 = () => {
      if (p + 4 > extBytes.length) return null;
      const v = ((extBytes[p] << 24) | (extBytes[p+1] << 16) | (extBytes[p+2] << 8) | extBytes[p+3]) >>> 0;
      p += 4;
      return v;
    };
    const readU24 = () => {
      if (p + 3 > extBytes.length) return null;
      const v = ((extBytes[p] << 16) | (extBytes[p+1] << 8) | extBytes[p+2]) >>> 0;
      p += 3;
      return v;
    };

    if (flags & 0x0200) out.creationDateTimeExt32 = readU32();
    if (flags & 0x0100) out.expiryExt32 = readU32();
    if (flags & 0x0080) out.readerIdExt32 = readU32();
    if (flags & 0x0040) out.managementExt32 = readU32();
    if (flags & 0x0020) {
      out.locationLatExt24 = readU24();
      out.locationLonExt24 = readU24();
    }
    if (flags & 0x0010) out.municipalityExt24 = readU24();

    return out;
  }

  // ===== マトリックスから全ステップをまとめて復号 =====
  function decodeFromMatrix(mat, opts) {
    opts = opts || {};
    const N = mat.length;
    if (N === 0 || mat[0].length !== N) throw new Error('DM: 非正方行列');
    const symbol = getSymbolBySize(N);
    if (!symbol) throw new Error('DM: 未対応シンボルサイズ ' + N);

    // (A) マッピング領域抽出
    const mapping = extractMappingFromCells(mat, symbol);
    // (B) Utah 逆配置でコード語列 (data+ECC) を復元
    const finalCwArr = extractCodewordsFromMapping(mapping);
    const finalCwLen = symbol.data + symbol.ecc;
    const finalCw = finalCwArr.slice(0, finalCwLen);
    // (C) XOR マスク逆適用
    const unmasked = opts.xorMask
      ? applyXorMask(finalCw, opts.xorMask)
      : finalCw.slice();
    // (D) 逆インターリーブ + RS 訂正
    const { dataCw, errors } = deinterleaveAndCorrect(unmasked, symbol);
    // (E) ストリームパース
    const parsed = parseDataStream(dataCw);
    const ext = parseExtBlocks(parsed.extBytes, parsed.managementCode32);

    return {
      size: N,
      symbol,
      codewords: unmasked,
      dataCodewords: dataCw,
      rsErrors: errors,
      data: parsed.data,
      dataBytes: parsed.dataBytes,
      dataEncoding: parsed.dataEncoding,
      managementCode32: parsed.managementCode32,
      extBytes: parsed.extBytes,
      ...ext
    };
  }

  // ===== 画像サンプリング =====
  //
  // QR Matrix 画像からの DM サンプリング:
  //   QR の 4 コーナー (QR セル座標 (0,0)-(NQR,NQR) に対応する画像ピクセル位置)
  //   を基に透視変換を作り、DM セルの中心点をサンプル。
  //
  // DM 位置 (QR 座標系):
  //   dmOrigin = NQR - NDM + 1.5
  //   DM (dr, dc) の中心 = (dmOrigin + dc + 0.5, dmOrigin + dr + 0.5)  [回転後座標]
  //   元 DM: DM_orig(r, c) = DM_rot(NDM-1-c, r)  ← CCW 回転の逆
  //
  // NDM は未知なので、L字ファインダー (回転後の下辺 dr=NDM-1 と右辺 dc=NDM-1)
  // のセルが画像上で暗いかをテストして、最適な NDM を選ぶ。

  // 4 点 (src) → 4 点 (dst) の透視変換行列 3x3 を返す (row-major)
  // src: [[sx0,sy0],[sx1,sy1],[sx2,sy2],[sx3,sy3]]
  // dst: 同上
  function perspectiveTransform(src, dst) {
    // src → dst の変換: まず単位正方形 → src, 単位正方形 → dst を作り、合成
    // 単純化のため、直接 8x8 連立を解く
    const a = [];
    const b = [];
    for (let i = 0; i < 4; i++) {
      const [sx, sy] = src[i];
      const [dx, dy] = dst[i];
      a.push([sx, sy, 1, 0, 0, 0, -dx * sx, -dx * sy]); b.push(dx);
      a.push([0, 0, 0, sx, sy, 1, -dy * sx, -dy * sy]); b.push(dy);
    }
    // ガウス消去
    const n = 8;
    for (let i = 0; i < n; i++) {
      let piv = i;
      for (let k = i + 1; k < n; k++) if (Math.abs(a[k][i]) > Math.abs(a[piv][i])) piv = k;
      if (piv !== i) { [a[i], a[piv]] = [a[piv], a[i]]; [b[i], b[piv]] = [b[piv], b[i]]; }
      const d = a[i][i];
      if (Math.abs(d) < 1e-12) throw new Error('透視変換: 特異行列');
      for (let j = i; j < n; j++) a[i][j] /= d;
      b[i] /= d;
      for (let k = 0; k < n; k++) {
        if (k === i) continue;
        const f = a[k][i];
        if (!f) continue;
        for (let j = i; j < n; j++) a[k][j] -= f * a[i][j];
        b[k] -= f * b[i];
      }
    }
    return [
      b[0], b[1], b[2],
      b[3], b[4], b[5],
      b[6], b[7], 1
    ];
  }

  function applyTransform(H, x, y) {
    const w = H[6] * x + H[7] * y + H[8];
    return [
      (H[0] * x + H[1] * y + H[2]) / w,
      (H[3] * x + H[4] * y + H[5]) / w
    ];
  }

  // imageData から輝度 (0-255) を取得
  function luma(imageData, x, y) {
    const { width, height, data } = imageData;
    const ix = Math.round(x), iy = Math.round(y);
    if (ix < 0 || ix >= width || iy < 0 || iy >= height) return 255;
    const o = (iy * width + ix) * 4;
    return (data[o] * 299 + data[o+1] * 587 + data[o+2] * 114) / 1000;
  }

  // 画像全体から二値化閾値 (Otsu 近似 / 簡易平均)
  function computeThreshold(imageData, samples) {
    const { width, height, data } = imageData;
    samples = samples || 2000;
    let sum = 0, cnt = 0;
    for (let i = 0; i < samples; i++) {
      const x = Math.floor(Math.random() * width);
      const y = Math.floor(Math.random() * height);
      const o = (y * width + x) * 4;
      sum += (data[o] * 299 + data[o+1] * 587 + data[o+2] * 114) / 1000;
      cnt++;
    }
    return sum / cnt;
  }

  // QR の 4 コーナー (QR セル座標 0..NQR) を画像ピクセル座標に対応づける透視変換を作る。
  // qrLocation は jsQR の location オブジェクト (topLeftCorner など)。
  function buildQRTransform(qrLocation, NQR) {
    // QR Matrix 用: DM が右下に重なっているため、jsQR が返す bottomRightCorner は
    // 破損した alignment pattern から推定されて不正確なことが多い。
    // 代わりに 3 つの finder pattern 中心 (TL=(3,3), TR=(NQR-4,3), BL=(3,NQR-4)) を
    // 使って affine 変換を組み立て、4 コーナーを外挿して perspective 変換を得る。
    //
    // finder 中心がすべて利用可能 → 3 点から affine 変換 (a,b,c,d,e,f) を解く:
    //   x = a*u + b*v + c
    //   y = d*u + e*v + f
    // 3 点 → 6 式 で a..f が決定。
    const {
      topLeftFinderPattern: TL,
      topRightFinderPattern: TR,
      bottomLeftFinderPattern: BL,
      topLeftCorner, topRightCorner, bottomRightCorner, bottomLeftCorner
    } = qrLocation;

    if (TL && TR && BL) {
      const u1 = 3.5, v1 = 3.5;           // TL finder center (cell 3 center)
      const u2 = NQR - 3.5, v2 = 3.5;     // TR finder center
      const u3 = 3.5, v3 = NQR - 3.5;     // BL finder center
      // x 方程式: a*u + b*v + c = x_i (3 式)
      // TL, TR で (u1,v1)=(3.5,3.5), (u2,v2)=(NQR-3.5,3.5)
      // → a*(NQR-7) = TR.x - TL.x → a = (TR.x - TL.x)/(NQR-7)
      // TL, BL で 同様 → b = (BL.x - TL.x)/(NQR-7)
      // c = TL.x - a*3.5 - b*3.5
      const a = (TR.x - TL.x) / (NQR - 7);
      const b = (BL.x - TL.x) / (NQR - 7);
      const c = TL.x - a * 3.5 - b * 3.5;
      const d = (TR.y - TL.y) / (NQR - 7);
      const e = (BL.y - TL.y) / (NQR - 7);
      const f = TL.y - d * 3.5 - e * 3.5;
      const mapCell = (u, v) => [a * u + b * v + c, d * u + e * v + f];
      const src = [[0, 0], [NQR, 0], [NQR, NQR], [0, NQR]];
      const dst = [ mapCell(0, 0), mapCell(NQR, 0), mapCell(NQR, NQR), mapCell(0, NQR) ];
      return perspectiveTransform(src, dst);
    }

    // fallback: jsQR の 4 コーナー
    const src = [[0, 0], [NQR, 0], [NQR, NQR], [0, NQR]];
    const dst = [
      [topLeftCorner.x, topLeftCorner.y],
      [topRightCorner.x, topRightCorner.y],
      [bottomRightCorner.x, bottomRightCorner.y],
      [bottomLeftCorner.x, bottomLeftCorner.y]
    ];
    return perspectiveTransform(src, dst);
  }

  // 指定された NDM に対し fit スコアを評価する。
  //
  // 要点: DM の L字右下隅は全ての NDM 候補で同じ画像位置 (NQR+0.5, NQR+0.5) にある
  //       ため、それだけでは候補を区別できない。代わりに「DM 内側」の特徴を見る:
  //         (a) 回転後の TOP timing 行 (dr=0, 内部列): 交互黒白 (dc=0:黒, dc=1:白, ...)
  //             assembleFinalSymbol: clock(上辺) は i%2===0 で黒
  //         (b) 回転後の LEFT timing 列 (dc=0, 内部行): 交互黒白
  //             clock(右辺) は (regionDataRows+1-i)%2===0 で黒。回転後は左辺に相当。
  //         (c) 「DM の 1 セル外側」の行/列 (QR 座標で r=NQR-NDM, c=NQR-NDM)
  //             これは QR 本体領域の 1 行/列。NDM によって異なる位置になるので
  //             そこを参考にはしない (誤検出の原因になる)。
  //         (d) DM 内部セル中心は「概ね 50% 黒」→ 全体の平均 dark 率で補助判定。
  //
  //   NDM が正しい → (a)(b) のパターン一致率が高く、(d) の dark 率が ~0.5
  //   NDM が小さすぎ → (a)(b) は DM データ領域を見ることになり、パターン一致率 ~0.5
  //   NDM が大きすぎ → (a)(b) は QR 領域を見ることになり、パターン一致率 ~0.5
  function scoreNDM(imageData, H, NQR, NDM, threshold) {
    const dmOrigin = NQR - NDM + 1.5;
    const sampleDark = (cx, cy) => {
      const [px, py] = applyTransform(H, cx, cy);
      return luma(imageData, px, py) < threshold;
    };

    // Rendered (rotated CCW) DM の構造:
    //   TOP row  (dr=0)    : timing  (.#.#.#.#... → dc%2===1 が黒)
    //   LEFT col (dc=0)    : timing  (.#.#.#.#... → dr%2===1 が黒)
    //   BOTTOM row (dr=N-1): L-finder (全黒)
    //   RIGHT col (dc=N-1) : L-finder (全黒)

    // (a) Top timing row
    let tMatch = 0, tTotal = 0;
    for (let dc = 1; dc < NDM - 1; dc++) {
      const dark = sampleDark(dmOrigin + dc + 0.5, dmOrigin + 0.5);
      if (dark === (dc % 2 === 1)) tMatch++;
      tTotal++;
    }
    // (b) Left timing col
    for (let dr = 1; dr < NDM - 1; dr++) {
      const dark = sampleDark(dmOrigin + 0.5, dmOrigin + dr + 0.5);
      if (dark === (dr % 2 === 1)) tMatch++;
      tTotal++;
    }
    // (c) Bottom L-finder (全黒期待)
    let lMatch = 0, lTotal = 0;
    for (let dc = 0; dc < NDM; dc++) {
      const dark = sampleDark(dmOrigin + dc + 0.5, dmOrigin + (NDM - 1) + 0.5);
      if (dark) lMatch++;
      lTotal++;
    }
    // (d) Right L-finder (全黒期待)
    for (let dr = 0; dr < NDM - 1; dr++) {
      const dark = sampleDark(dmOrigin + (NDM - 1) + 0.5, dmOrigin + dr + 0.5);
      if (dark) lMatch++;
      lTotal++;
    }
    // (e) 内部 dark 率 (~0.5 期待)
    let dAll = 0, tAll = 0;
    for (let dr = 1; dr < NDM - 1; dr++) {
      for (let dc = 1; dc < NDM - 1; dc++) {
        if (sampleDark(dmOrigin + dc + 0.5, dmOrigin + dr + 0.5)) dAll++;
        tAll++;
      }
    }
    const dRate = dAll / Math.max(1, tAll);

    const tScore = tTotal > 0 ? tMatch / tTotal : 0.5;
    const lScore = lTotal > 0 ? lMatch / lTotal : 0.5;
    const dScoreDist = 1 - Math.abs(dRate - 0.5) * 2;
    // 重み: L-finder (0.5) + timing (0.35) + dark 率 (0.15)
    return lScore * 0.5 + tScore * 0.35 + dScoreDist * 0.15;
  }

  // 画像 + QR 検出結果から NDM を推定
  function detectNDM(imageData, qrLocation, NQR, opts) {
    opts = opts || {};
    const threshold = opts.threshold || computeThreshold(imageData);
    const H = buildQRTransform(qrLocation, NQR);
    const candidates = DM_SYMBOLS
      .map(s => s.size)
      .filter(n => n <= NQR - 8);
    let bestScore = -1, bestN = -1;
    for (const n of candidates) {
      const s = scoreNDM(imageData, H, NQR, n, threshold);
      if (s > bestScore) { bestScore = s; bestN = n; }
    }
    return { NDM: bestN, score: bestScore, threshold, H };
  }

  // DM を画像からサンプリング → bool[NDM][NDM] (回転済みの状態)
  function sampleDMMatrix(imageData, H, NQR, NDM, threshold) {
    const dmOrigin = NQR - NDM + 1.5;
    const dmRot = [];
    for (let dr = 0; dr < NDM; dr++) {
      const row = new Array(NDM);
      for (let dc = 0; dc < NDM; dc++) {
        const cx = dmOrigin + dc + 0.5;
        const cy = dmOrigin + dr + 0.5;
        const [px, py] = applyTransform(H, cx, cy);
        row[dc] = luma(imageData, px, py) < threshold;
      }
      dmRot.push(row);
    }
    return dmRot;
  }

  // 回転済み DM → 元 DM (CCW 逆 = CW 回転)
  // dm.js: out[N-1-c][r] = in[r][c]  → CCW
  // 逆: orig[r][c] = rot[N-1-c][r]
  function rotateDMCW(dmRot) {
    const N = dmRot.length;
    const out = [];
    for (let r = 0; r < N; r++) {
      const row = new Array(N);
      for (let c = 0; c < N; c++) row[c] = dmRot[N - 1 - c][r];
      out.push(row);
    }
    return out;
  }

  // ===== トップレベル: 画像 + QR 検出結果から DM 情報を復号 =====
  function decodeFromImage(imageData, qrLocation, NQR, opts) {
    opts = opts || {};
    const det = detectNDM(imageData, qrLocation, NQR, opts);
    if (det.NDM < 0) throw new Error('DM サイズの推定に失敗しました');
    const dmRot = sampleDMMatrix(imageData, det.H, NQR, det.NDM, det.threshold);
    const dmOrig = rotateDMCW(dmRot);
    const result = decodeFromMatrix(dmOrig, opts);
    result.NDM = det.NDM;
    result.detectScore = det.score;
    result.threshold = det.threshold;
    return result;
  }

  // ===== Export =====
  const dmdecode = {
    // 高レベル
    decodeFromImage,
    decodeFromMatrix,
    detectNDM,
    sampleDMMatrix,
    rotateDMCW,
    // 低レベル (テスト・再利用用)
    extractMappingFromCells,
    extractCodewordsFromMapping,
    deinterleaveAndCorrect,
    applyXorMask,
    rsDecode,
    parseDataStream,
    parseExtBlocks,
    decodeBase256,
    bytesToString,
    buildQRTransform,
    applyTransform,
    perspectiveTransform,
    // 定数
    DM_SYMBOLS,
    getSymbolBySize
  };

  global.dmdecode = dmdecode;
})(typeof window !== 'undefined' ? window : (typeof global !== 'undefined' ? global : this));
