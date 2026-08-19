/* ============================================================
   TeX parser for non_mf_groups_exist.tex
   Parse pass: structure + numbering + labels.
   Render pass lives in ui.js.
   ============================================================ */
'use strict';

const DIAG = { warnings: [], mathErrors: [] };
function warn(msg) { DIAG.warnings.push(msg); console.warn('[paper]', msg); }

/* ---------- low-level scanning helpers ---------- */

function findMatchingBrace(src, i) {
  // src[i] === '{'; returns index of matching '}'
  let depth = 0;
  for (let k = i; k < src.length; k++) {
    const c = src[k];
    if (c === '\\') { k++; continue; }
    if (c === '{') depth++;
    else if (c === '}') { depth--; if (depth === 0) return k; }
  }
  return -1;
}

function grabGroup(src, i) {
  // skip whitespace, expect '{...}'; returns {content, next} or null
  while (i < src.length && /\s/.test(src[i])) i++;
  if (src[i] !== '{') return null;
  const j = findMatchingBrace(src, i);
  if (j < 0) return null;
  return { content: src.slice(i + 1, j), next: j + 1 };
}

function grabOpt(src, i) {
  // skip whitespace, optionally grab '[...]' (bracket-nesting-aware via brace skip)
  let k = i;
  while (k < src.length && /\s/.test(src[k])) k++;
  if (src[k] !== '[') return null;
  let depth = 0;
  for (let m = k; m < src.length; m++) {
    const c = src[m];
    if (c === '\\') { m++; continue; }
    if (c === '{') { const j = findMatchingBrace(src, m); if (j > 0) { m = j; continue; } }
    if (c === '[') depth++;
    else if (c === ']') { depth--; if (depth === 0) return { content: src.slice(k + 1, m), next: m + 1 }; }
  }
  return null;
}

/* ---------- comment stripping (TeX semantics) ---------- */

function stripComments(tex) {
  const lines = tex.split('\n');
  const out = [];
  let carry = null;  // pending line whose newline was eaten by a mid-line comment
  for (const raw of lines) {
    let line = raw;
    if (carry !== null) { line = carry + line.replace(/^\s*/, ''); carry = null; }
    let cut = -1;
    for (let k = 0; k < line.length; k++) {
      if (line[k] === '\\') { k++; continue; }
      if (line[k] === '%') { cut = k; break; }
    }
    if (cut < 0) { out.push(line); continue; }
    const before = line.slice(0, cut);
    if (/^\s*$/.test(before)) continue;  // whole-line comment: vanishes, no phantom paragraph break
    carry = before;                      // TeX: comment eats the newline and the next line's indent
  }
  if (carry !== null) out.push(carry);
  return out.join('\n');
}

/* ---------- document extraction ---------- */

function extractDocument(tex) {
  const bodyStart = tex.indexOf('\\section{Introduction}');
  const bibStart = tex.indexOf('\\begin{thebibliography}');
  const bibEnd = tex.indexOf('\\end{thebibliography}');
  const absStart = tex.indexOf('\\begin{abstract}');
  const absEnd = tex.indexOf('\\end{abstract}');
  if (bodyStart < 0 || bibStart < 0) throw new Error('document landmarks not found');
  return {
    abstract: tex.slice(absStart + '\\begin{abstract}'.length, absEnd),
    body: tex.slice(bodyStart, bibStart),
    bib: tex.slice(bibStart + '\\begin{thebibliography}'.length, bibEnd),
  };
}

/* ---------- leanverified extraction ---------- */

function extractLean(src) {
  // returns {clean, lean:[{module,decl}]}
  const lean = [];
  let clean = '';
  let i = 0;
  while (i < src.length) {
    const k = src.indexOf('\\leanverified', i);
    if (k < 0) { clean += src.slice(i); break; }
    clean += src.slice(i, k);
    const g1 = grabGroup(src, k + '\\leanverified'.length);
    if (!g1) { warn('malformed leanverified'); i = k + 13; continue; }
    const g2 = grabGroup(src, g1.next);
    if (!g2) { warn('malformed leanverified 2'); i = g1.next; continue; }
    lean.push({ module: g1.content.trim(), decl: g2.content.trim() });
    i = g2.next;
  }
  return { clean, lean };
}

/* A \leanverified run written just after \end{theorem} or \end{proof},
   with nothing but whitespace in between, annotates the environment it
   follows — there is no other step between it and that \end.  Adopt it
   onto that node, so the formalization reaches the badge on the statement
   or the Proof line instead of clumping into a paragraph of loose,
   identical check marks that name nothing.  Returns the new cursor. */
function adoptTrailingLean(src, from, node) {
  let i = from;
  for (;;) {
    let j = i;
    while (j < src.length && /\s/.test(src[j])) j++;
    if (!src.startsWith('\\leanverified', j)) break;
    const g1 = grabGroup(src, j + '\\leanverified'.length);
    if (!g1) break;
    const g2 = grabGroup(src, g1.next);
    if (!g2) break;
    node.lean.push({ module: g1.content.trim(), decl: g2.content.trim() });
    node.leanTrailing = (node.leanTrailing || 0) + 1;
    i = g2.next;
  }
  return i;
}

/* ---------- sentences ---------- */

/* The manuscript is graded sentence by sentence, and the grading keys on the
   sentence's own text, so the renderer has to cut a paragraph into sentences
   exactly where the census cut it.  Same guarded split: a period inside
   mathematics, inside a macro argument, inside an abbreviation or inside a
   decimal does not end a sentence. */
const ABBREV = ['cf', 'e.g', 'i.e', 'etc', 'vs', 'resp', 'Prop', 'Thm', 'Def', 'Cor',
  'Lem', 'Ch', 'Sec', 'Fig', 'Eq', 'no', 'No', 'al', 'Mr', 'Dr', 'St',
  'Jr', 'approx', 'Ex', 'cca', 'Ph.D', 'pp', 'vol', 'ed', 'eds', 'Op'];

function protectPeriods(text) {
  text = text.replace(/\$[^$]*\$/g, m => m.replace(/\./g, '\u0000'));
  text = text.replace(/\\[a-zA-Z]+\s*\{[^{}]*\}/g, m => m.replace(/\./g, '\u0000'));
  for (const a of ABBREV) text = text.split(a + '.').join(a + '\u0000');
  text = text.replace(/(?<=\d)\.(?=\d)/g, '\u0000');
  return text;
}

function splitSentences(paragraph) {
  const guarded = protectPeriods(paragraph);
  return guarded.split(/(?<=[.!?])["'\)\}]?\s+/)
    .map(p => p.split('\u0000').join('.').trim())
    .filter(Boolean);
}

/* FNV-1a over UTF-8 of the whitespace-collapsed sentence: the same key the
   build computes from the census. */
function sentenceKey(sentence) {
  // the badges are metadata sitting inside the sentence, not part of it
  const bare = sentence
    .replace(/\\leanverified\s*\{[^{}]*\}\s*\{[^{}]*\}/g, '')
    .replace(/\\leanstep\s*\{[^{}]*\}/g, '');
  const norm = bare.replace(/\s+/g, ' ').trim();
  const bytes = new TextEncoder().encode(norm);
  let h = 0x811c9dc5;
  for (const b of bytes) {
    h = Math.imul(h ^ b, 0x01000193) >>> 0;
  }
  return h.toString(16).padStart(8, '0');
}

/* ---------- numbering state ---------- */

const THM_ENVS = {
  theorem: 'Theorem', proposition: 'Proposition', lemma: 'Lemma',
  corollary: 'Corollary', definition: 'Definition',
  construction: 'Construction', remark: 'Remark', mainthm: 'Theorem',
};
const MATH_ENVS = ['equation', 'gather', 'gather*', 'align', 'align*'];

class Counters {
  constructor() {
    this.section = 0; this.sub = 0; this.thm = 0; this.eq = 0;
    this.mainthm = 0; this.fig = 0; this.supplement = false;
  }
  secLabel() { return (this.supplement ? 'S' : '') + this.section; }
  stepSection() { this.section++; this.sub = 0; this.thm = 0; return this.secLabel(); }
  stepSub() { this.sub++; return this.secLabel() + '.' + this.sub; }
  stepThm() { this.thm++; return this.secLabel() + '.' + this.thm; }
  stepMain() { this.mainthm++; return String.fromCharCode(64 + this.mainthm); }
  stepEq() { this.eq++; return String(this.eq); }
  enterSupplement() { this.supplement = true; this.section = 0; }
}

/* ---------- label registry ---------- */

const LABELS = {};  // label -> {num, kind, anchor}
function registerLabels(labels, num, kind, anchor) {
  for (const l of labels) {
    if (LABELS[l]) warn('duplicate label ' + l);
    LABELS[l] = { num, kind, anchor };
  }
}

/* ---------- extract \label{}s from a chunk (removing them) ---------- */

function pullLabels(src) {
  const labels = [];
  const clean = src.replace(/\\label\{([^}]*)\}/g, (m, l) => { labels.push(l.trim()); return ''; });
  return { clean, labels };
}

/* ---------- main block parser ---------- */

let ANCHOR_SEQ = 0;
const ANCHOR_USED = new Set();
function mkAnchor(prefix, hint) {
  const slug = (hint || '').toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '').slice(0, 40);
  let a = prefix + '-' + (slug || ++ANCHOR_SEQ);
  while (ANCHOR_USED.has(a)) a = a + '-' + (++ANCHOR_SEQ);
  ANCHOR_USED.add(a);
  return a;
}

function parseBlocks(src, C) {
  // returns array of nodes
  const nodes = [];
  let i = 0;
  let paraBuf = '';
  const flushPara = () => {
    const parts = paraBuf.split(/\n\s*\n/);
    for (const p of parts) {
      const t = p.trim();
      if (t) nodes.push({ t: 'para', src: t });
    }
    paraBuf = '';
  };

  const RE = /\\(section|subsection)(\*?)\{|\\paragraph\{|\\begin\{([a-zA-Z*]+)\}|\\\[|\\item\b|\\(clearpage|newpage|bigskip|medskip|smallskip|maketitle|tableofcontents)\b|\\begingroup|\\setcounter\{section\}\{0\}|\\renewcommand|\\addcontentsline/g;

  while (i < src.length) {
    RE.lastIndex = i;
    const m = RE.exec(src);
    if (!m) { paraBuf += src.slice(i); break; }
    // check the match isn't escaped (preceded by backslash-escaping? our tokens start with backslash already; fine)
    paraBuf += src.slice(i, m.index);
    i = m.index;

    if (m[1]) {  // \section or \subsection
      flushPara();
      const star = m[2] === '*';
      const braceAt = i + m[0].length - 1;
      const j = findMatchingBrace(src, braceAt);
      let title = src.slice(braceAt + 1, j);
      i = j + 1;
      // trailing \label{}s
      let labels = [];
      let rest = src.slice(i);
      const lm = rest.match(/^\s*(?:\\label\{[^}]*\}\s*)+/);
      if (lm) {
        const pulled = pullLabels(lm[0]);
        labels = pulled.labels;
        i += lm[0].length;
      }
      const inTitle = pullLabels(title); title = inTitle.clean; labels.push(...inTitle.labels);
      let num = null;
      const kind = m[1];
      if (!star) num = (kind === 'section') ? C.stepSection() : C.stepSub();
      else if (kind === 'section' && C.section === 0 && !C.supplement) { /* unnumbered before 1? no-op */ }
      const anchor = mkAnchor(kind === 'section' ? 'sec' : 'sub', labels[0] || title);
      registerLabels(labels, num, kind, anchor);
      nodes.push({ t: kind, star, title, labels, num, anchor });
      continue;
    }

    if (m[0] === '\\paragraph{') {
      flushPara();
      const braceAt = i + m[0].length - 1;
      const j = findMatchingBrace(src, braceAt);
      const title = src.slice(braceAt + 1, j);
      i = j + 1;
      nodes.push({ t: 'paragraph', title });
      continue;
    }

    if (m[3]) {  // \begin{ENV}
      const env = m[3];
      const endTok = '\\end{' + env + '}';
      if (env in THM_ENVS) {
        flushPara();
        let j = i + m[0].length;
        const opt = grabOpt(src, j);
        let title = null;
        if (opt) { title = opt.content; j = opt.next; }
        const endAt = src.indexOf(endTok, j);
        if (endAt < 0) throw new Error('unclosed ' + env);
        let inner = src.slice(j, endAt);
        i = endAt + endTok.length;
        const le = extractLean(inner); inner = le.clean;
        // leading labels
        let labels = [];
        const lm = inner.match(/^\s*(?:\\label\{[^}]*\}\s*)+/);
        if (lm) { const pulled = pullLabels(lm[0]); labels = pulled.labels; inner = inner.slice(lm[0].length); }
        const num = env === 'mainthm' ? C.stepMain() : C.stepThm();
        const anchor = mkAnchor('thm', labels[0] || (THM_ENVS[env] + '-' + num));
        registerLabels(labels, num, THM_ENVS[env], anchor);
        const body = parseBlocks(inner, C);
        const node = { t: 'thm', env, name: THM_ENVS[env], title, labels, num, anchor, lean: le.lean, body };
        i = adoptTrailingLean(src, i, node);
        nodes.push(node);
        continue;
      }
      if (env === 'proof') {
        flushPara();
        let j = i + m[0].length;
        const opt = grabOpt(src, j);
        let title = null;
        if (opt) { title = opt.content; j = opt.next; }
        const endAt = src.indexOf(endTok, j);
        if (endAt < 0) throw new Error('unclosed proof');
        let inner = src.slice(j, endAt);
        i = endAt + endTok.length;
        // collect the markers for the Proof-line badge, but leave them in
        // the text: the inline renderer places a chip at the exact step
        // each marker annotates
        const le = extractLean(inner);
        const body = parseBlocks(inner, C);
        const node = { t: 'proof', title, lean: le.lean, inlineLean: le.lean.length, body };
        i = adoptTrailingLean(src, i, node);
        nodes.push(node);
        continue;
      }
      if (env === 'enumerate' || env === 'itemize') {
        flushPara();
        let j = i + m[0].length;
        const opt = grabOpt(src, j);
        if (opt) j = opt.next;
        // find matching end (envs can nest same-type? assume not for lists of same kind)
        const endAt = src.indexOf(endTok, j);
        if (endAt < 0) throw new Error('unclosed ' + env);
        const inner = src.slice(j, endAt);
        i = endAt + endTok.length;
        nodes.push(parseList(inner, env, C));
        continue;
      }
      if (env === 'quote' || env === 'quotation') {
        flushPara();
        const j = i + m[0].length;
        const endAt = src.indexOf(endTok, j);
        if (endAt < 0) throw new Error('unclosed ' + env);
        const inner = src.slice(j, endAt);
        i = endAt + endTok.length;
        nodes.push({ t: 'quote', body: parseBlocks(inner, C) });
        continue;
      }
      if (MATH_ENVS.includes(env)) {
        flushPara();
        const j = i + m[0].length;
        const endAt = src.indexOf(endTok, j);
        if (endAt < 0) throw new Error('unclosed ' + env);
        let inner = src.slice(j, endAt);
        i = endAt + endTok.length;
        nodes.push(mkDisplayMath(env, inner, C));
        continue;
      }
      if (env === 'figure') {
        flushPara();
        const endAt = src.indexOf('\\end{figure}', i);
        const inner = src.slice(i, endAt);
        i = endAt + '\\end{figure}'.length;
        // caption + label
        const capAt = inner.indexOf('\\caption');
        let caption = '';
        if (capAt >= 0) { const g = grabGroup(inner, capAt + '\\caption'.length); if (g) caption = g.content; }
        const labs = [...inner.matchAll(/\\label\{([^}]*)\}/g)].map(x => x[1]);
        C.fig++;
        const num = String(C.fig);
        const anchor = 'fig-' + num;
        registerLabels(labs, num, 'Figure', anchor);
        nodes.push({ t: 'figure', num, caption, labels: labs, anchor });
        continue;
      }
      if (env === 'gathered' || env === 'aligned' || env === 'pmatrix' || env === 'cases' || env === 'smallmatrix') {
        // inner math env encountered at top level — shouldn't happen; treat as text
        paraBuf += m[0]; i += m[0].length; continue;
      }
      // unknown environment: swallow begin, warn
      warn('unknown environment ' + env);
      paraBuf += m[0]; i += m[0].length;
      continue;
    }

    if (m[0] === '\\[') {
      flushPara();
      const endAt = src.indexOf('\\]', i + 2);
      if (endAt < 0) throw new Error('unclosed \\[');
      const inner = src.slice(i + 2, endAt);
      i = endAt + 2;
      nodes.push(mkDisplayMath('\\[', inner, C));
      continue;
    }

    if (m[0] === '\\item' || m[0].startsWith('\\item')) {
      // \item outside a list context — parseList handles items; here it means we are inside parseList's inner call
      // Shouldn't reach; treat as text.
      paraBuf += ' '; i += m[0].length;
      continue;
    }

    if (m[4]) {  // spacing / page commands
      if (m[4] === 'bigskip' || m[4] === 'medskip') { flushPara(); nodes.push({ t: 'vspace' }); }
      i += m[0].length;
      continue;
    }

    if (m[0] === '\\begingroup') {
      // the supplement divider block: \begingroup \centering \bfseries\Large Supplementary material\par \endgroup
      const endAt = src.indexOf('\\endgroup', i);
      const inner = src.slice(i, endAt >= 0 ? endAt : i + 12);
      if (/Supplementary material/.test(inner)) {
        flushPara();
        nodes.push({ t: 'divider', title: 'Supplementary material' });
        i = endAt + '\\endgroup'.length;
      } else {
        i += '\\begingroup'.length;
      }
      continue;
    }

    if (m[0] === '\\setcounter{section}{0}') {
      C.enterSupplement();
      i += m[0].length;
      continue;
    }

    if (m[0] === '\\renewcommand' || m[0] === '\\addcontentsline') {
      // swallow with its groups
      let j = i + m[0].length;
      for (let n = 0; n < 3; n++) {
        const g = grabGroup(src, j);
        if (!g) break;
        j = g.next;
        // \renewcommand takes 2 groups; \addcontentsline takes 3
        if (m[0] === '\\renewcommand' && n === 1) break;
      }
      i = j;
      continue;
    }

    // fallthrough
    paraBuf += m[0];
    i += m[0].length;
  }
  flushPara();
  return nodes;
}

function parseList(inner, kind, C) {
  // split on \item at depth 0
  const items = [];
  let i = 0;
  let cur = null;
  while (i < inner.length) {
    const k = findTopLevelItem(inner, i);
    if (k < 0) { if (cur) cur.src += inner.slice(i); else if (inner.slice(i).trim()) warn('list preamble text dropped'); break; }
    if (cur) cur.src += inner.slice(i, k);
    else if (inner.slice(i, k).trim()) warn('list preamble text dropped');
    let j = k + '\\item'.length;
    const opt = grabOpt(inner, j);
    let label = null;
    if (opt) { label = opt.content; j = opt.next; }
    cur = { label, src: '' };
    items.push(cur);
    i = j;
  }
  return {
    t: 'list', kind,
    items: items.map(it => ({ label: it.label, body: parseBlocks(it.src, C) })),
  };
}

function findTopLevelItem(src, from) {
  // find next \item not inside a nested environment or math
  let depth = 0;
  for (let i = from; i < src.length; i++) {
    if (src[i] !== '\\') continue;
    const rest = src.slice(i, i + 12);
    if (rest.startsWith('\\begin{')) { depth++; i += 6; continue; }
    if (rest.startsWith('\\end{')) { depth--; i += 4; continue; }
    if (rest.startsWith('\\[')) { depth++; i++; continue; }
    if (rest.startsWith('\\]')) { depth--; i++; continue; }
    if (depth === 0 && rest.startsWith('\\item') && !/[a-zA-Z]/.test(src[i + 5] || '')) return i;
    if (rest.startsWith('\\\\')) { i++; continue; }
  }
  return -1;
}

function mkDisplayMath(env, inner, C) {
  const pulled = pullLabels(inner);
  let src = pulled.clean;
  const labels = pulled.labels;
  let num = null, tag = null;
  // \tag{...} overrides; amsmath: \tag does not step the counter
  const tm = src.match(/\\tag\{((?:[^{}]|\{[^{}]*\})*)\}/);
  if (tm) {
    tag = tm[1].replace(/\\ensuremath\{([^{}]*)\}/g, '$1')
      .replace(/\\ast\b/g, '∗').replace(/\\star\b/g, '⋆').replace(/\\dagger\b/g, '†').trim();
    src = src.replace(tm[0], '');
  }
  if (env === 'equation' && !tag) num = C.stepEq();
  const anchor = labels.length ? mkAnchor('eq', labels[0]) : null;
  if (labels.length) registerLabels(labels, num || tag, 'eq', anchor);
  // wrap for KaTeX
  let katexSrc;
  if (env === '\\[' || env === 'equation') katexSrc = src;
  else katexSrc = '\\begin{' + env.replace('*', '') + '*}' + src + '\\end{' + env.replace('*', '') + '*}';
  // gather/align without star but with our external numbering: the paper only uses
  // starred forms plus `equation`, so this is exhaustive.
  return { t: 'dmath', env, src, katexSrc, num, tag, labels, anchor };
}

/* ---------- bibliography ---------- */

function parseBib(src) {
  const entries = [];
  const re = /\\bibitem\[([^\]]*)\]\{([^}]*)\}/g;
  let m, prev = null;
  while ((m = re.exec(src))) {
    if (prev) prev.src = src.slice(prev.end, m.index).trim();
    prev = { label: m[1], key: m[2], end: re.lastIndex };
    entries.push(prev);
  }
  if (prev) prev.src = src.slice(prev.end).trim();
  const byKey = {};
  for (const e of entries) byKey[e.key] = e;
  return { entries, byKey };
}

/* ---------- top-level parse ---------- */

function parsePaper(tex) {
  const stripped = stripComments(tex);
  const doc = extractDocument(stripped);
  const C = new Counters();
  const nodes = parseBlocks(doc.body, C);
  const bib = parseBib(doc.bib);
  return { abstract: doc.abstract, nodes, bib, counters: C };
}
