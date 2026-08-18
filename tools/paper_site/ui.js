/* ============================================================
   Render + UI for the non-MF paper site.
   Depends on parser.js (parsePaper, LABELS, DIAG) and KaTeX.
   ============================================================ */
'use strict';

/* ---------- KaTeX ---------- */

const MACROS = {
  '\\C': '\\mathbb{C}', '\\Z': '\\mathbb{Z}', '\\R': '\\mathbb{R}', '\\N': '\\mathbb{N}',
  '\\SL': '\\operatorname{SL}', '\\GL': '\\operatorname{GL}', '\\U': '\\mathcal{U}',
  '\\Fix': '\\operatorname{Fix}', '\\tr': '\\operatorname{tr}', '\\Ad': '\\operatorname{Ad}',
  '\\End': '\\operatorname{End}', '\\Cl': '\\operatorname{Cl}',
  '\\Cmax': 'C^*_{\\mathrm{max}}', '\\Cred': 'C^*_{\\mathrm{r}}',
  '\\opnorm': '\\left\\lVert #1\\right\\rVert', '\\hsnorm': '\\left\\lVert #1\\right\\rVert_{2}',
  '\\varinjlim': '\\mathop{\\underset{\\longrightarrow}{\\lim}}',
  '\\textup': '\\text{#1}',
};

function resolveMathRefs(src) {
  src = src.replace(/\\qedhere\b/g, '');
  // KaTeX has no \ref/\eqref; substitute the resolved printed number
  return src.replace(/\\(eqref|ref)\{([^}]*)\}/g, (m, kind, label) => {
    const rec = LABELS[label.trim()];
    if (!rec) { warn('unresolved math \\' + kind + '{' + label + '}'); return '\\text{??}'; }
    const num = rec.num == null ? '?' : String(rec.num);
    return (kind === 'eqref' || rec.kind === 'eq') ? '\\text{(' + num + ')}' : '\\text{' + num + '}';
  });
}

function tex2html(src, display) {
  src = resolveMathRefs(src);
  try {
    katex.__parse(src, { macros: Object.assign({}, MACROS), displayMode: !!display, strict: false });
  } catch (e) {
    DIAG.mathErrors.push({ src: src.slice(0, 120), err: String(e).slice(0, 200) });
  }
  return katex.renderToString(src, {
    macros: Object.assign({}, MACROS),
    displayMode: !!display,
    throwOnError: false,
    strict: false,
    trust: false,
  });
}

/* ---------- inline text rendering ---------- */

function escHtml(s) {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

function typographize(s) {
  // applied to plain-text runs only (already HTML-escaped)
  return s
    .replace(/---/g, '—')
    .replace(/([0-9])--([0-9])/g, '$1–$2')
    .replace(/--/g, '–')
    .replace(/``/g, '“').replace(/''/g, '”')
    .replace(/(^|[\s(—])`/g, '$1‘').replace(/`/g, '‘')
    .replace(/'/g, '’')
    .replace(/~/g, ' ');
}


function glueAfterMath(src, i, mathHtml) {
  // punctuation or a -suffix straight after math must not wrap to the next line
  const m = src.slice(i).match(/^([,.;:!?)\]]+|-[a-zA-Z]+)/);
  if (!m) return { html: mathHtml, next: i };
  return { html: '<span class="nobr">' + mathHtml + typographize(escHtml(m[1])) + '</span>', next: i + m[1].length };
}

function renderInline(src, ctx) {
  ctx = ctx || {};
  let out = '';
  let i = 0;
  let plain = '';
  const flush = () => { out += typographize(escHtml(plain)); plain = ''; };

  while (i < src.length) {
    const c = src[i];

    if (c === '$') {
      flush();
      // find closing unescaped $
      let j = i + 1;
      for (; j < src.length; j++) {
        if (src[j] === '\\') { j++; continue; }
        if (src[j] === '$') break;
      }
      const math = src.slice(i + 1, j);
      const glued = glueAfterMath(src, j + 1, tex2html(math, false));
      out += glued.html;
      i = glued.next;
      continue;
    }

    if (c === '{') {
      flush();
      const j = findMatchingBrace(src, i);
      if (j < 0) { plain += c; i++; continue; }
      let inner = src.slice(i + 1, j);
      i = j + 1;
      // leading style switches inside the group
      const st = inner.match(/^\s*\\(footnotesize|small|bfseries|itshape|scshape|Large|large|em)\b/);
      if (st) {
        inner = inner.slice(st[0].length);
        const cls = { footnotesize: 'x-small', small: 'x-small', bfseries: 'x-bold', itshape: 'x-it', scshape: 'x-sc', Large: 'x-large', large: 'x-large', em: 'x-it' }[st[1]];
        out += '<span class="' + cls + '">' + renderInline(inner, ctx) + '</span>';
      } else {
        out += renderInline(inner, ctx);
      }
      continue;
    }

    if (c !== '\\') { plain += c; i++; continue; }

    // command
    const m = src.slice(i).match(/^\\([a-zA-Z@]+)\s*/);
    if (!m) {
      // escaped single char
      const ch = src[i + 1] || '';
      if (ch === '(') {                              // \( ... \) inline math
        flush();
        const j = src.indexOf('\\)', i + 2);
        if (j < 0) { warn('unclosed \\('); plain += '('; i += 2; continue; }
        const glued = glueAfterMath(src, j + 2, tex2html(src.slice(i + 2, j), false));
        out += glued.html;
        i = glued.next;
        continue;
      }
      if (ch === '\\') { flush(); out += '<br>'; i += 2; continue; }
      if ('&%$#_{} '.includes(ch)) { plain += ch === ' ' ? ' ' : ch; i += 2; continue; }
      if (ch === ',') { flush(); out += ' '; i += 2; continue; }
      if (ch === ';') { flush(); out += ' '; i += 2; continue; }
      if (ch === '@') { i += 2; continue; }
      if (ch === '-') { i += 2; continue; }  // discretionary hyphen
      if (ch === '~') { plain += '~'; i += 2; continue; }
      plain += ch; i += 2; continue;
    }

    const cmd = m[1];
    i += 1 + cmd.length;                                   // past "\cmd"
    while (i < src.length && /\s/.test(src[i])) i++;       // TeX eats whitespace after a control word

    const takeGroup = () => { const g = grabGroup(src, i); if (g) { i = g.next; return g.content; } return null; };
    const takeOpt = () => { const g = grabOpt(src, i); if (g) { i = g.next; return g.content; } return null; };

    switch (cmd) {
      case 'emph': { flush(); const a = takeGroup(); out += '<em>' + renderInline(a || '', ctx) + '</em>'; break; }
      case 'textbf': { flush(); const a = takeGroup(); out += '<strong>' + renderInline(a || '', ctx) + '</strong>'; break; }
      case 'textit': { flush(); const a = takeGroup(); out += '<em>' + renderInline(a || '', ctx) + '</em>'; break; }
      case 'textup': case 'textrm': case 'textnormal': { flush(); const a = takeGroup(); out += '<span class="x-up">' + renderInline(a || '', ctx) + '</span>'; break; }
      case 'texttt': { flush(); const a = takeGroup(); out += '<code>' + renderInline(a || '', ctx) + '</code>'; break; }
      case 'textsc': { flush(); const a = takeGroup(); out += '<span class="x-sc">' + renderInline(a || '', ctx) + '</span>'; break; }
      case 'texorpdfstring': { flush(); const a = takeGroup(); takeGroup(); out += renderInline(a || '', ctx); break; }
      case 'ensuremath': { flush(); const a = takeGroup(); out += tex2html(a || '', false); break; }
      case 'ref': {
        flush(); const a = (takeGroup() || '').trim();
        out += xrefHtml(a, null);
        break;
      }
      case 'eqref': {
        flush(); const a = (takeGroup() || '').trim();
        out += xrefHtml(a, 'eq');
        break;
      }
      case 'cite': {
        flush();
        const opt = takeOpt();
        const keys = (takeGroup() || '').split(',').map(s => s.trim()).filter(Boolean);
        const parts = keys.map(k => {
          const e = BIB.byKey[k];
          if (!e) { warn('unknown citation ' + k); return '<span class="unk">' + escHtml(k) + '</span>'; }
          return '<a class="cite" href="#bib-' + escHtml(k) + '" data-key="' + escHtml(k) + '">' + escHtml(e.label) + '</a>';
        });
        out += '[' + parts.join(', ');
        if (opt) out += ', ' + renderInline(opt, ctx);
        out += ']';
        break;
      }
      case 'label': {
        const a = (takeGroup() || '').trim();
        flush(); out += '<span class="inline-anchor" id="lab-' + escHtml(a.replace(/[^a-zA-Z0-9:_-]/g, '')) + '"></span>';
        if (!LABELS[a]) warn('inline label unregistered: ' + a);
        break;
      }
      case 'doi': { flush(); const a = takeGroup() || ''; out += '<a class="ext" href="https://doi.org/' + escHtml(a) + '" target="_blank" rel="noopener">doi:' + escHtml(a) + '</a>'; break; }
      case 'arxiv': { flush(); const a = takeGroup() || ''; out += '<a class="ext" href="https://arxiv.org/abs/' + escHtml(a) + '" target="_blank" rel="noopener">arXiv:' + escHtml(a) + '</a>'; break; }
      case 'url': { flush(); const a = takeGroup() || ''; out += '<a class="ext" href="' + escHtml(a) + '" target="_blank" rel="noopener">' + escHtml(a) + '</a>'; break; }
      case 'href': { flush(); const u = takeGroup() || ''; const t = takeGroup() || u; out += '<a class="ext" href="' + escHtml(u) + '" target="_blank" rel="noopener">' + renderInline(t, ctx) + '</a>'; break; }
      case 'nolinkurl': { flush(); const a = takeGroup() || ''; out += escHtml(a); break; }
      case 'footnote': { flush(); const a = takeGroup() || ''; out += '<span class="fnote">(' + renderInline(a, ctx) + ')</span>'; break; }
      case 'qedhere': { if (ctx.env) ctx.env.qedhere = true; break; }
      case 'leanverified': { takeGroup(); takeGroup(); break; }
      case 'S': { flush(); out += '§'; break; }
      case 'dots': case 'ldots': { flush(); out += '…'; break; }
      case 'o': { plain += 'ø'; break; }
      case 'O': { plain += 'Ø'; break; }
      case 'ae': { plain += 'æ'; break; }
      case 'aa': { plain += 'å'; break; }
      case 'ss': { plain += 'ß'; break; }
      case '@': break;
      case 'colon': { plain += ': '; break; }
      case 'noindent': case 'centering': case 'raggedright': case 'ignorespaces': case 'relax':
      case 'clearpage': case 'newpage': case 'smallskip': case 'medskip': case 'bigskip':
      case 'allowbreak': case 'par': case 'indent': case 'protect': case 'maketitle':
        break;
      case 'phantom': case 'vphantom': case 'hphantom': { takeGroup(); break; }
      case 'setcounter': case 'addtocounter': { takeGroup(); takeGroup(); break; }
      case 'renewcommand': case 'newcommand': case 'providecommand': { takeGroup(); takeOpt(); takeGroup(); break; }
      case 'addcontentsline': { takeGroup(); takeGroup(); takeGroup(); break; }
      case 'footnotesize': case 'small': case 'normalsize': case 'large': case 'Large': case 'bfseries': case 'itshape': case 'scshape': case 'em':
        break; // bare style switch outside group: ignore (rare)
      default: {
        warn('unknown text command \\' + cmd + ' near: ' + src.slice(Math.max(0, i - 30), i + 20).replace(/\s+/g, ' '));
        flush();
        out += '<code class="unk">\\' + escHtml(cmd) + '</code>';
      }
    }
  }
  flush();
  return out;
}

function xrefHtml(label, mode) {
  const rec = LABELS[label];
  if (!rec) {
    warn('unresolved \\ref{' + label + '}');
    return '<span class="unk">??' + escHtml(label) + '</span>';
  }
  let text = rec.num == null ? '?' : String(rec.num);
  if (mode === 'eq' || rec.kind === 'eq') text = '(' + text + ')';
  return '<a class="xref" href="#' + rec.anchor + '" data-label="' + escHtml(label) + '">' + escHtml(text) + '</a>';
}

/* ---------- block rendering ---------- */

const PLAIN_STYLE = { theorem: 1, proposition: 1, lemma: 1, corollary: 1, mainthm: 1 };

function renderNodes(nodes, ctx) {
  let out = '';
  for (let idx = 0; idx < nodes.length; idx++) {
    const n = nodes[idx];
    out += renderNode(n, ctx, nodes, idx);
  }
  return out;
}

function renderNode(n, ctx, siblings, idx) {
  switch (n.t) {
    case 'section': {
      const numHtml = n.num ? '<span class="secnum">' + escHtml(n.num) + '</span>' : '';
      return '<h2 class="sec" id="' + n.anchor + '">' + numHtml + '<span>' + renderInline(n.title, ctx) + '</span></h2>';
    }
    case 'subsection': {
      const numHtml = n.num ? '<span class="secnum">' + escHtml(n.num) + '</span>' : '';
      return '<h3 class="subsec" id="' + n.anchor + '">' + numHtml + '<span>' + renderInline(n.title, ctx) + '</span></h3>';
    }
    case 'divider':
      return '<div class="part-divider" id="supplement"><span>' + escHtml(n.title) + '</span></div>';
    case 'para': {
      const c = Object.assign({}, ctx);
      const html = renderInline(n.src, c);
      if (!html.trim()) return '';
      return '<p>' + html + '</p>';
    }
    case 'dmath': {
      const id = n.anchor ? ' id="' + n.anchor + '"' : '';
      const no = n.tag || n.num;
      const eqno = no ? '<span class="eqno">(' + escHtml(no) + ')</span>' : '';
      return '<div class="dmath"' + id + '>' + eqno + '<div class="dmath-scroll">' + tex2html(n.katexSrc, true) + '</div></div>';
    }
    case 'list': {
      if (n.kind === 'itemize') {
        return '<ul class="tex-ul">' + n.items.map(it =>
          '<li>' + renderNodes(it.body, ctx) + '</li>').join('') + '</ul>';
      }
      return '<ol class="tex-ol">' + n.items.map((it, k) => {
        const lab = it.label != null ? renderInline(it.label, ctx) : '(' + (k + 1) + ')';
        return '<li><span class="li-label">' + lab + '</span><div class="li-body">' + renderNodes(it.body, ctx) + '</div></li>';
      }).join('') + '</ol>';
    }
    case 'paragraph':
      return '<h4 class="para-head">' + renderInline(n.title, ctx) + '</h4>';
    case 'thm': return renderThm(n, ctx);
    case 'proof': return renderProof(n, ctx);
    case 'figure': return renderFigure(n, ctx);
    case 'vspace': return '<div class="vspace"></div>';
    default:
      warn('unknown node type ' + n.t);
      return '';
  }
}


const GITHUB_BLOB = 'https://github.com/SauersML/group-approximation/blob/main/GroupApproximation/';
function leanDeclHtml(l) {
  const code = (window.LEAN_SRC || {})[l.module + '|' + l.declaration];
  const link = '<a class="lean-mod" href="' + GITHUB_BLOB + escHtml(l.module) + '.lean" target="_blank" rel="noopener">' + escHtml(l.module) + '.lean</a>';
  if (!code) return '<div class="lean-decl">' + link + escHtml(l.declaration) + '</div>';
  return '<details class="lean-decl"><summary>' + escHtml(l.declaration) + '</summary>' +
    '<pre class="lean-code">' + escHtml(code) + '</pre>' + link + '</details>';
}

function claimForThm(n) {
  if (!window.CLAIMS) return null;
  for (const lab of n.labels) {
    const c = CLAIMS.claims.find(c => c.id === lab);
    if (c) return c;
  }
  return null;
}

function renderThm(n, ctx) {
  const claim = claimForThm(n);
  const style = PLAIN_STYLE[n.env] ? 'thm-plain' : (n.env === 'remark' ? 'thm-remark' : 'thm-def');
  let head = '<span class="thm-name">' + escHtml(n.name) + ' ' + escHtml(n.num) + '</span>';
  if (n.title) head += ' <span class="thm-title">(' + renderInline(n.title, ctx) + ')</span>';
  head += '<span class="thm-dot">.</span>';
  let badges = '<span class="thm-tools">';
  if (claim) badges += '<button class="badge badge-lean" data-claim="' + escHtml(claim.id) + '" title="Machine-checked in Lean 4">Lean&thinsp;✓</button>';
  badges += '</span>';
  const c = Object.assign({}, ctx, { env: n });
  const body = renderNodes(n.body, c);
  return '<section class="thm ' + style + ' thm-' + n.env + '" id="' + n.anchor + '" data-labels="' + escHtml(n.labels.join(' ')) + '">' +
    '<div class="thm-head">' + head + badges + '</div>' +
    '<div class="thm-stmt">' + body + '</div>' +
    '</section>';
}

function renderProof(n, ctx) {
  const c = Object.assign({}, ctx, { env: n });
  let body = renderNodes(n.body, c);
  const title = n.title ? renderInline(n.title, c) : 'Proof';
  // tombstone
  body += '<span class="qed" title="end of proof">∎</span>';
  return '<details class="proof" open><summary><span class="proof-label">' + title + '.</span></summary><div class="proof-body">' + body + '</div></details>';
}

/* ---------- the figure (hand-converted from TikZ) ---------- */

function renderFigure(n, ctx) {
  const S = 54;                     // px per cm
  const X = x => (x + 0.55) * S;
  const Y = y => (3.35 - y) * S;
  const R = 9;                      // c/d circle radius (tight, as in the TikZ inner sep)
  const W = Math.round(X(11.3)), H = Math.round(Y(-2.05));
  const shapes = `
  <defs><marker id="figarrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6.5" markerHeight="6.5" orient="auto-start-reverse">
    <path d="M0,0 L10,5 L0,10 z" fill="currentColor"></path></marker></defs>
  <rect x="${X(0)}" y="${Y(3.1)}" width="${6.5 * S}" height="${3.1 * S}" rx="8" fill="none" stroke="currentColor" stroke-width="1"></rect>
  <rect x="${X(2.95)}" y="${Y(2.4)}" width="${3.2 * S}" height="${1.95 * S}" rx="6" fill="none" stroke="currentColor" stroke-width="1"></rect>
  <line x1="${X(1.75)}" y1="${Y(2.62)}" x2="${X(3.3)}" y2="${Y(2.62)}" stroke="currentColor" stroke-width="1" marker-end="url(#figarrow)"></line>
  <circle cx="${X(1.35)}" cy="${Y(-1.5)}" r="${R}" fill="none" stroke="currentColor" stroke-width="1"></circle>
  <circle cx="${X(4.55)}" cy="${Y(-1.5)}" r="${R}" fill="none" stroke="currentColor" stroke-width="1"></circle>
  <line x1="${X(1.35) + R + 1}" y1="${Y(-1.5)}" x2="${X(4.55) - R - 2}" y2="${Y(-1.5)}" stroke="currentColor" stroke-width="1" marker-end="url(#figarrow)"></line>
  <line x1="${X(1.35)}" y1="${Y(-1.5) - R}" x2="${X(1.35)}" y2="${Y(0)}" stroke="currentColor" stroke-width="1"></line>
  <line x1="${X(4.55)}" y1="${Y(-1.5) - R}" x2="${X(4.55)}" y2="${Y(0.45)}" stroke="currentColor" stroke-width="1"></line>
  <path d="M ${X(4.55) + R + 1} ${Y(-1.5)} H ${X(9.35)} V ${Y(-0.28)}" fill="none" stroke="currentColor" stroke-width="1" marker-end="url(#figarrow)"></path>`;
  const labels = [
    { x: 1.05, y: 2.68, tex: '\\iota(\\mathcal B)', cls: 'fig-note' },
    { x: 4.55, y: 1.62, tex: 't\\iota(\\mathcal B)t^{-1}' },
    { x: 1.35, y: 1.15, tex: '\\iota(v_1)' },
    { x: 2.52, y: 2.87, tex: 't(\\,\\cdot\\,)t^{-1}', cls: 'fig-tiny' },
    { x: 1.35, y: -1.5, tex: 'c', cls: 'fig-note fig-clear' },
    { x: 4.55, y: -1.5, tex: 'd', cls: 'fig-note fig-clear' },
    { x: 2.95, y: -1.78, html: 'conjugation by ' + tex2html('t', false), cls: 'fig-tiny' },
    { x: 1.16, y: -0.68, tex: '[c,\\iota(\\mathcal B)]=1', anchor: 'e', cls: 'fig-note' },
    { x: 4.74, y: -0.68, tex: '[\\,d,\\,t\\iota(\\mathcal B)t^{-1}]=1', anchor: 'w', cls: 'fig-note' },
  ];
  let overlay = labels.map(l => {
    const html = l.html || tex2html(l.tex, false);
    const anchor = l.anchor || 'c';
    const style = 'left:' + X(l.x).toFixed(1) + 'px;top:' + Y(l.y).toFixed(1) + 'px;';
    return '<div class="fig-label fig-a-' + anchor + ' ' + (l.cls || '') + '" style="' + style + '">' + html + '</div>';
  }).join('');
  // the outlined "distinguished word" box
  const witnessRef = xrefHtml('prop:witness', null);
  overlay += '<div class="fig-mark" style="left:' + X(9.35).toFixed(1) + 'px;top:' + Y(1.05).toFixed(1) + 'px;">' +
    '<div>distinguished word</div>' +
    '<div>' + tex2html('w=[\\,d,\\ \\iota(v_1)\\,d\\,\\iota(v_1)^{-1}]', false) + '</div>' +
    '<div>' + tex2html('=[\\,d,\\iota(v_1)]^{\\,2}', false) + ' since ' + tex2html('d^2=1', false) + ';</div>' +
    '<div>nontrivial by</div>' +
    '<div>Proposition ' + witnessRef + '</div></div>';

  const caption = renderInline(n.caption, ctx);
  return '<figure class="paper-fig" id="' + n.anchor + '">' +
    '<div class="fig-scale"><div class="fig-canvas" style="width:' + W + 'px;height:' + H + 'px" data-w="' + W + '" data-h="' + H + '">' +
    '<svg viewBox="0 0 ' + W + ' ' + H + '" width="' + W + '" height="' + H + '" role="img" aria-label="The one-sided conjugation configuration.">' + shapes + '</svg>' +
    overlay + '</div></div>' +
    '<figcaption><span class="fig-no">Figure ' + escHtml(n.num) + '.</span> ' + caption + '</figcaption></figure>';
}

function fitFigures() {
  document.querySelectorAll('.fig-scale').forEach(wrap => {
    const canvas = wrap.querySelector('.fig-canvas');
    const w = +canvas.dataset.w, h = +canvas.dataset.h;
    const k = Math.min(1, wrap.clientWidth / w);
    canvas.style.transform = 'scale(' + k + ')';
    canvas.style.transformOrigin = '0 0';
    wrap.style.height = (h * k) + 'px';
  });
}

/* ---------- bibliography rendering ---------- */

let BIB = { entries: [], byKey: {} };

function renderBib() {
  let out = '<h2 class="sec" id="bibliography"><span>References</span></h2><dl class="bib">';
  for (const e of BIB.entries) {
    out += '<div class="bib-row" id="bib-' + escHtml(e.key) + '">' +
      '<dt>[' + escHtml(e.label) + ']</dt><dd>' + renderInline(e.src.replace(/\s+/g, ' '), {}) + '</dd></div>';
  }
  return out + '</dl>';
}

/* ---------- table of contents ---------- */

function buildToc(nodes) {
  const items = [];
  for (const n of nodes) {
    if (n.t === 'divider') items.push({ kind: 'divider' });
    if (n.t === 'section') items.push({ kind: 'sec', num: n.num, title: n.title, anchor: n.anchor });
    if (n.t === 'thm' && n.env === 'mainthm') items.push({ kind: 'mainthm', num: n.num, title: n.title, anchor: n.anchor });
  }
  let html = '<nav class="toc" aria-label="Contents"><ul>';
  html += '<li class="toc-sec"><a href="#top" data-anchor="top">Abstract</a></li>';
  for (const it of items) {
    if (it.kind === 'divider') { html += '<li class="toc-divider">Supplement</li>'; continue; }
    if (it.kind === 'mainthm') continue;
    html += '<li class="toc-sec"><a href="#' + it.anchor + '" data-anchor="' + it.anchor + '">' +
      (it.num ? '<span class="toc-num">' + escHtml(it.num) + '</span>' : '') +
      '<span>' + renderInline(it.title, {}) + '</span></a></li>';
  }
  html += '<li class="toc-sec"><a href="#bibliography" data-anchor="bibliography"><span>References</span></a></li>';
  html += '</ul></nav>';
  return html;
}

/* ---------- claims view ---------- */

function claimNum(id) { return LABELS[id] ? LABELS[id].num : null; }

function buildUsedBy() {
  const used = {};
  const deps = window.__graphDeps || {};
  for (const id in deps) for (const d of deps[id]) (used[d] = used[d] || []).push(id);
  return used;
}

function envOfClaim(c) { return c.environment === 'mainthm' ? 'theorem' : c.environment; }

function buildClaimsView() {
  const usedBy = buildUsedBy();
  const kinds = [...new Set(CLAIMS.claims.map(envOfClaim))].sort();
  let html = '<div class="claims-bar"><input id="claims-search" type="search" placeholder="Filter" aria-label="Filter claims">' +
    '<div class="claims-filters">' + kinds.map(k =>
      '<button class="chip chip-filter is-on" data-kind="' + k + '">' + k + '</button>').join('') + '</div></div>';
  html += '<div class="claims-count" id="claims-count"></div><div class="claims-grid">';
  for (const c of CLAIMS.claims) {
    const num = claimNum(c.id);
    const name = (c.environment === 'mainthm' ? 'Theorem' : c.environment[0].toUpperCase() + c.environment.slice(1)) + ' ' + (num || '?');
    const anchor = LABELS[c.id] ? LABELS[c.id].anchor : '';
    const deps = (window.__graphDeps[c.id] || []).map(d => xrefClaimChip(d)).join('');
    const ub = (usedBy[c.id] || []).map(d => xrefClaimChip(d)).join('');
    const decls = (c.lean || []).map(leanDeclHtml).join('');
    html += '<article class="claim-card" data-kind="' + envOfClaim(c) + '" data-id="' + escHtml(c.id) + '">' +
      '<header><a class="claim-name" href="#' + anchor + '">' + escHtml(name) + '</a>' +
      (c.title ? '<span class="claim-title">' + escHtml(c.title) + '</span>' : '') +
      '</header>' +
      '<div class="claim-stmt" data-anchor="' + anchor + '"></div>' +
      '<div class="claim-meta">' +
      (deps ? '<div class="claim-deps"><span class="meta-label">uses</span>' + deps + '</div>' : '') +
      (ub ? '<div class="claim-deps"><span class="meta-label">used by</span>' + ub + '</div>' : '') +
      decls +
      '</div></article>';
  }
  html += '</div>';
  return html;
}

const KIND_ABBR = { Theorem: 'Thm', Proposition: 'Prop', Lemma: 'Lem', Corollary: 'Cor', Definition: 'Def', Construction: 'Constr', Remark: 'Rem', Figure: 'Fig' };
function xrefClaimChip(id) {
  const num = claimNum(id);
  const rec = LABELS[id];
  const abbr = rec && rec.kind !== 'eq' ? (KIND_ABBR[rec.kind] || rec.kind) : '';
  const txt = num != null ? (abbr ? abbr + ' ' + num : '(' + num + ')') : id;
  return '<a class="chip chip-ref" href="#' + (rec ? rec.anchor : '') + '" data-label="' + escHtml(id) + '">' + escHtml(String(txt)) + '</a>';
}

/* ---------- dependency graph ---------- */

function computeGraphDeps() {
  const idset = new Set(CLAIMS.claims.map(c => c.id));
  const deps = {};
  for (const c of CLAIMS.claims) deps[c.id] = new Set((c.dependencies || []).filter(d => idset.has(d)));
  // a proof's cross-references are dependencies of the claim it proves
  document.querySelectorAll('#paper-body details.proof').forEach(p => {
    let owner = null;
    const t = p.querySelector('summary a.xref');
    if (t && idset.has(t.dataset.label)) owner = t.dataset.label;
    if (!owner) {
      let el = p.previousElementSibling;
      while (el && !el.classList.contains('thm') && el.tagName !== 'H2') el = el.previousElementSibling;
      if (el && el.classList.contains('thm')) {
        const lab = (el.dataset.labels || '').split(' ').find(l => idset.has(l));
        if (lab) owner = lab;
      }
    }
    if (!owner) return;
    p.querySelectorAll('.proof-body a.xref').forEach(a => {
      const l = a.dataset.label;
      if (idset.has(l) && l !== owner) deps[owner].add(l);
    });
  });
  const out = {};
  for (const k in deps) out[k] = [...deps[k]];
  return out;
}


function buildGraph() {
  const ids = CLAIMS.claims.map(c => c.id);
  const deps = window.__graphDeps;
  // longest-path layering
  const layer = {};
  const depth = id => {
    if (layer[id] != null) return layer[id];
    layer[id] = 0; // cycle guard
    layer[id] = deps[id].length ? Math.max(...deps[id].map(depth)) + 1 : 0;
    return layer[id];
  };
  ids.forEach(depth);
  const maxL = Math.max(...ids.map(i => layer[i]));
  const cols = [];
  for (let l = 0; l <= maxL; l++) cols.push(ids.filter(i => layer[i] === l));
  // barycenter ordering sweeps
  const pos = {};
  cols.forEach(col => col.forEach((id, k) => pos[id] = k));
  for (let sweep = 0; sweep < 6; sweep++) {
    for (let l = 1; l <= maxL; l++) {
      cols[l].sort((a, b) => bary(a) - bary(b));
      cols[l].forEach((id, k) => pos[id] = k);
    }
    for (let l = maxL - 1; l >= 0; l--) {
      const kids = {};
      ids.forEach(i => deps[i].forEach(d => (kids[d] = kids[d] || []).push(i)));
      cols[l].sort((a, b) => baryK(a, kids) - baryK(b, kids));
      cols[l].forEach((id, k) => pos[id] = k);
    }
  }
  function bary(id) { const ds = deps[id]; return ds.length ? ds.reduce((s, d) => s + pos[d], 0) / ds.length : pos[id]; }
  function baryK(id, kids) { const ks = kids[id] || []; return ks.length ? ks.reduce((s, d) => s + pos[d], 0) / ks.length : pos[id]; }

  const CW = 152, RH = 40, PADX = 24, PADY = 20;
  const maxRows = Math.max(...cols.map(c => c.length));
  const W = PADX * 2 + (maxL + 1) * CW;
  const H = PADY * 2 + maxRows * RH;
  const xy = {};
  cols.forEach((col, l) => {
    const off = (maxRows - col.length) / 2;
    col.forEach((id, k) => xy[id] = { x: PADX + l * CW + 60, y: PADY + (off + k) * RH + RH / 2 });
  });

  let edges = '';
  for (const c of CLAIMS.claims) for (const d of (deps[c.id] || [])) {
    const a = xy[d], b = xy[c.id];
    const mx = (a.x + b.x) / 2;
    edges += '<path class="g-edge" data-from="' + escHtml(d) + '" data-to="' + escHtml(c.id) + '" d="M ' + (a.x + 52) + ' ' + a.y +
      ' C ' + mx + ' ' + a.y + ' ' + mx + ' ' + b.y + ' ' + (b.x - 52) + ' ' + b.y + '"></path>';
  }
  let nodesHtml = '';
  for (const c of CLAIMS.claims) {
    const p = xy[c.id];
    const num = claimNum(c.id) || '?';
    const short = (c.environment === 'mainthm' ? 'Thm' : { theorem: 'Thm', proposition: 'Prop', lemma: 'Lem', corollary: 'Cor', definition: 'Def', construction: 'Constr', remark: 'Rem' }[c.environment] || c.environment);
    const supp = String(num).startsWith('S');
    nodesHtml += '<g class="g-node' + (supp ? ' g-supp' : '') + '" data-id="' + escHtml(c.id) + '" transform="translate(' + p.x + ',' + p.y + ')">' +
      '<rect x="-52" y="-15" width="104" height="30" rx="7"></rect>' +
      '<text text-anchor="middle" dy="4">' + escHtml(short + ' ' + num) + '</text>' +
      '<title>' + escHtml((c.title || c.id)) + '</title></g>';
  }
  return '<div class="graph-help">Edges run from what a claim uses to the claim. Click a node to trace it; click it again to open the statement.</div>' +
    '<div class="graph-legend"><span class="lg lg-main"></span> main paper <span class="lg lg-supp"></span> supplement</div>' +
    '<div class="graph-wrap"><svg id="depgraph" viewBox="0 0 ' + W + ' ' + H + '" preserveAspectRatio="xMidYMid meet">' + edges + nodesHtml + '</svg></div>' +
    '<aside class="graph-panel" id="graph-panel" hidden></aside>';
}

/* ---------- hover preview ---------- */

let hoverCard = null;
function setupHoverPreviews(root) {
  hoverCard = document.createElement('div');
  hoverCard.className = 'hover-card';
  hoverCard.hidden = true;
  document.body.appendChild(hoverCard);
  let hideTimer = null;

  function show(target, html) {
    clearTimeout(hideTimer);
    hoverCard.innerHTML = html;
    hoverCard.hidden = false;
    const r = target.getBoundingClientRect();
    const cw = Math.min(560, window.innerWidth - 24);
    hoverCard.style.maxWidth = cw + 'px';
    hoverCard.style.left = '0px'; hoverCard.style.top = '0px';
    // measure then place
    const hw = hoverCard.offsetWidth, hh = hoverCard.offsetHeight;
    let x = Math.min(r.left, window.innerWidth - hw - 12);
    let y = r.bottom + 8;
    if (y + hh > window.innerHeight - 8) y = r.top - hh - 8;
    hoverCard.style.left = Math.max(8, x) + 'px';
    hoverCard.style.top = Math.max(8, y + window.scrollY) + 'px';
  }
  function hide() { hideTimer = setTimeout(() => { hoverCard.hidden = true; }, 120); }

  root.addEventListener('mouseover', ev => {
    const a = ev.target.closest('.xref, .cite');
    if (!a) return;
    let html = null;
    if (a.classList.contains('cite')) {
      const e = BIB.byKey[a.dataset.key];
      if (e) html = '<div class="hc-bib">[' + escHtml(e.label) + '] ' + renderInline(e.src.replace(/\s+/g, ' '), {}) + '</div>';
    } else {
      const rec = LABELS[a.dataset.label];
      if (rec) {
        const tgt = document.getElementById(rec.anchor);
        if (tgt) {
          if (tgt.classList.contains('thm')) {
            const head = tgt.querySelector('.thm-head');
            const stmt = tgt.querySelector('.thm-stmt');
            html = '<div class="hc-thm"><div class="hc-head">' + head.innerHTML + '</div>' + stmt.innerHTML + '</div>';
          } else if (tgt.classList.contains('dmath')) {
            html = '<div class="hc-eq">' + tgt.innerHTML + '</div>';
          } else if (tgt.tagName === 'H2' || tgt.tagName === 'H3') {
            html = '<div class="hc-sec">§ ' + tgt.innerHTML + '</div>';
          } else if (tgt.classList.contains('paper-fig')) {
            html = '<div class="hc-sec">Figure ' + escHtml(rec.num) + '</div>';
          }
        }
      }
    }
    if (html) show(a, html);
  });
  root.addEventListener('mouseout', ev => {
    if (ev.target.closest('.xref, .cite')) hide();
  });
  hoverCard.addEventListener('mouseenter', () => clearTimeout(hideTimer));
  hoverCard.addEventListener('mouseleave', hide);
}

/* ---------- lean badge popover ---------- */

function setupLeanPopovers(root) {
  root.addEventListener('click', ev => {
    const b = ev.target.closest('.badge-lean');
    if (!b) { const p = document.querySelector('.lean-pop'); if (p && !ev.target.closest('.lean-pop')) p.remove(); return; }
    ev.preventDefault();
    const old = document.querySelector('.lean-pop');
    if (old) { old.remove(); if (old.dataset.for === b.dataset.claim) return; }
    const c = CLAIMS.claims.find(c => c.id === b.dataset.claim);
    if (!c) return;
    const usedBy = buildUsedBy();
    const pop = document.createElement('div');
    pop.className = 'lean-pop';
    pop.dataset.for = c.id;
    let html = '';
    for (const l of (c.lean || [])) html += leanDeclHtml(l);
    const cdeps = (window.__graphDeps[c.id] || []);
    if (cdeps.length) html += '<div class="claim-deps"><span class="meta-label">uses</span>' + cdeps.map(xrefClaimChip).join('') + '</div>';
    if ((usedBy[c.id] || []).length) html += '<div class="claim-deps"><span class="meta-label">used by</span>' + usedBy[c.id].map(xrefClaimChip).join('') + '</div>';
    pop.innerHTML = html;
    document.body.appendChild(pop);
    const r = b.getBoundingClientRect();
    const pw = pop.offsetWidth;
    pop.style.left = Math.max(8, Math.min(r.right - pw, window.innerWidth - pw - 12)) + 'px';
    pop.style.top = (r.bottom + 6 + window.scrollY) + 'px';
  });
}

/* ---------- init ---------- */

function init() {
  const t0 = performance.now();
  document.body.dataset.view = 'paper';
  const parsed = parsePaper(PAPER_TEX);
  BIB = parsed.bib;

  // ----- header/meta -----
  document.getElementById('abstract-body').innerHTML =
    parsed.abstract.split(/\n\s*\n/).map(p => p.trim() ? '<p>' + renderInline(p.trim(), {}) + '</p>' : '').join('');

  // ----- paper body -----
  const paperEl = document.getElementById('paper-body');
  paperEl.innerHTML = renderNodes(parsed.nodes, {}) + renderBib();

  // ----- toc -----
  document.getElementById('toc-slot').innerHTML = buildToc(parsed.nodes);

  // ----- claims + graph views -----
  window.__graphDeps = computeGraphDeps();
  document.getElementById('claims-content').innerHTML = buildClaimsView();
  document.getElementById('graph-content').innerHTML = buildGraph();

  // clone statements into claim cards
  document.querySelectorAll('.claim-stmt').forEach(el => {
    const tgt = document.getElementById(el.dataset.anchor);
    if (tgt) {
      const stmt = tgt.querySelector('.thm-stmt');
      if (stmt) el.innerHTML = stmt.innerHTML;
    }
  });

  fitFigures();
  window.addEventListener('resize', fitFigures);
  setupHoverPreviews(document.body);
  setupLeanPopovers(document.body);
  setupTabs();
  setupScrollSpy();
  setupClaimsFilter();
  setupGraphInteractions();

  const t1 = performance.now();
  console.log('[paper] rendered in', Math.round(t1 - t0), 'ms;',
    DIAG.warnings.length, 'warnings;', DIAG.mathErrors.length, 'math errors');
  if (DIAG.mathErrors.length) console.log('[paper] math errors:', DIAG.mathErrors);
  if (DIAG.warnings.length) console.log('[paper] warnings:', DIAG.warnings.slice(0, 50));
  window.__diag = DIAG;
}

/* ---------- interactions ---------- */

function setupTabs() {
  const tabs = document.querySelectorAll('.tab');
  const views = { paper: document.getElementById('view-paper'), claims: document.getElementById('view-claims'), graph: document.getElementById('view-graph') };
  tabs.forEach(t => t.addEventListener('click', () => {
    tabs.forEach(x => x.classList.toggle('is-on', x === t));
    for (const k in views) views[k].hidden = k !== t.dataset.view;
    document.body.dataset.view = t.dataset.view;
    if (t.dataset.view === 'paper') requestAnimationFrame(() => window.dispatchEvent(new Event('scroll')));
  }));
  // cross-view jumps: clicking an xref/chip while in claims/graph view switches to paper
  document.body.addEventListener('click', ev => {
    const a = ev.target.closest('a[href^="#"]');
    if (!a) return;
    const id = a.getAttribute('href').slice(1);
    const tgt = document.getElementById(id);
    if (!tgt) return;
    if (document.getElementById('view-paper').contains(tgt) && document.body.dataset.view !== 'paper') {
      document.querySelector('.tab[data-view="paper"]').click();
    }
    // flash target
    setTimeout(() => {
      tgt.classList.add('is-flash');
      setTimeout(() => tgt.classList.remove('is-flash'), 1600);
    }, 60);
  });
}

function setupScrollSpy() {
  const links = [...document.querySelectorAll('.toc a')];
  const byAnchor = {};
  links.forEach(l => byAnchor[l.dataset.anchor] = l);
  const marks = [...document.querySelectorAll('#view-paper h2[id], #view-paper .part-divider[id]')];
  let current = null;
  function onScroll() {
    if (document.body.dataset.view !== 'paper') return;
    let active = 'top';
    const fold = 120;
    for (const m of marks) {
      if (m.getBoundingClientRect().top <= fold) active = m.id;
      else break;
    }
    if (active === current) return;
    current = active;
    links.forEach(l => l.classList.toggle('is-active', l.dataset.anchor === active));
    const al = byAnchor[active];
    if (al) al.scrollIntoView({ block: 'nearest' });
  }
  document.addEventListener('scroll', onScroll, { passive: true });
  onScroll();
}

function setupClaimsFilter() {
  const input = document.getElementById('claims-search');
  const cards = [...document.querySelectorAll('.claim-card')];
  const count = document.getElementById('claims-count');
  const filters = [...document.querySelectorAll('.chip-filter')];
  function apply() {
    const q = input.value.trim().toLowerCase();
    const kinds = new Set(filters.filter(f => f.classList.contains('is-on')).map(f => f.dataset.kind));
    let n = 0;
    for (const c of cards) {
      const okKind = kinds.has(c.dataset.kind);
      const okText = !q || c.textContent.toLowerCase().includes(q) || c.dataset.id.toLowerCase().includes(q);
      const on = okKind && okText;
      c.hidden = !on;
      if (on) n++;
    }
    count.textContent = n === cards.length ? '' : n + ' of ' + cards.length;
  }
  input.addEventListener('input', apply);
  filters.forEach(f => f.addEventListener('click', () => { f.classList.toggle('is-on'); apply(); }));
  document.addEventListener('keydown', ev => {
    if (ev.key === '/' && document.body.dataset.view === 'claims' && document.activeElement !== input) {
      ev.preventDefault(); input.focus();
    }
  });
  apply();
}

function setupGraphInteractions() {
  const svg = document.getElementById('depgraph');
  if (!svg) return;
  const panel = document.getElementById('graph-panel');
  const deps = window.__graphDeps, kids = {};
  for (const id in deps) for (const d of deps[id]) (kids[d] = kids[d] || []).push(id);
  const closure = (start, rel) => {
    const seen = new Set(); const st = [start];
    while (st.length) { const x = st.pop(); for (const y of (rel[x] || [])) if (!seen.has(y)) { seen.add(y); st.push(y); } }
    return seen;
  };
  let selected = null;
  svg.addEventListener('click', ev => {
    const g = ev.target.closest('.g-node');
    if (!g) { clearSel(); return; }
    const id = g.dataset.id;
    if (selected === id) {
      // second click: jump to statement
      const rec = LABELS[id];
      if (rec) { document.querySelector('.tab[data-view="paper"]').click(); location.hash = '#' + rec.anchor; }
      return;
    }
    selected = id;
    const up = closure(id, deps), down = closure(id, kids);
    svg.querySelectorAll('.g-node').forEach(n => {
      n.classList.toggle('is-sel', n.dataset.id === id);
      n.classList.toggle('is-up', up.has(n.dataset.id));
      n.classList.toggle('is-down', down.has(n.dataset.id));
      n.classList.toggle('is-dim', n.dataset.id !== id && !up.has(n.dataset.id) && !down.has(n.dataset.id));
    });
    svg.querySelectorAll('.g-edge').forEach(e => {
      // edge points dep -> claim; upstream edges end at id or inside its dep closure,
      // downstream edges start at id or inside its user closure
      const onPath = (e.dataset.to === id || up.has(e.dataset.to)) ||
        (e.dataset.from === id || down.has(e.dataset.from));
      e.classList.toggle('is-hl', onPath);
      e.classList.toggle('is-dim', !onPath);
    });
    const c = CLAIMS.claims.find(x => x.id === id);
    const rec = LABELS[id];
    panel.hidden = false;
    panel.innerHTML = '<div class="gp-name">' + escHtml((rec ? rec.kind + ' ' + rec.num : id)) + (c.title ? ' <span class="claim-title">(' + escHtml(c.title) + ')</span>' : '') + '</div>' +
      '<div class="gp-counts">' + up.size + ' upstream · ' + down.size + ' downstream</div>';
  });
  function clearSel() {
    selected = null;
    panel.hidden = true;
    svg.querySelectorAll('.g-node, .g-edge').forEach(n => n.classList.remove('is-sel', 'is-up', 'is-down', 'is-dim', 'is-hl'));
  }
}

window.addEventListener('DOMContentLoaded', () => setTimeout(() => {
  try { init(); } catch (e) {
    console.error('[paper] init failed:', e);
    const el = document.getElementById('typesetting-note');
    if (el) el.textContent = 'Rendering failed — see the console: ' + e.message;
    throw e;
  }
}, 30));
