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

// for a double-quoted attribute value, where escHtml's three are not enough
function escAttr(s) {
  return escHtml(String(s)).replace(/"/g, '&quot;');
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
      case 'leanverified': {
        // a marker in running text is positional: this exact step is
        // machine-checked, so the chip sits right here.  Several markers in
        // a row annotate one and the same step, so they collapse into one
        // chip carrying a count — a row of identical check marks names
        // nothing, and the drawer lists the declarations by name.
        flush();
        const run = [{ module: (takeGroup() || '').trim(), decl: (takeGroup() || '').trim() }];
        for (;;) {
          let j = i;
          while (j < src.length && /\s/.test(src[j])) j++;
          if (!src.startsWith('\\leanverified', j)) break;
          const g1 = grabGroup(src, j + '\\leanverified'.length);
          if (!g1) break;
          const g2 = grabGroup(src, g1.next);
          if (!g2) break;
          run.push({ module: g1.content.trim(), decl: g2.content.trim() });
          i = g2.next;
        }
        out += leanChipHtml(run);
        break;
      }
      case 'leanstep': {
        // official positional metadata: the id names a row of the audited
        // proof-step ledger, and the chip's face reports that row's grade
        flush();
        const id = (takeGroup() || '').trim();
        const row = ledgerStep(id);
        if (!row) { warn('leanstep names no ledger row: ' + id); break; }
        const face = { 'EXACT': 'Lean&thinsp;✓', 'MISMATCH': 'Lean&thinsp;~' }[row.proof] || 'Lean&thinsp;–';
        const cls = { 'EXACT': '', 'MISMATCH': ' lean-chip-mismatch' }[row.proof] ?? ' lean-chip-missing';
        const title = {
          'EXACT': 'This step is machine-checked in Lean 4 — audited as exact',
          'MISMATCH': 'The Lean development proves this step by a different route — click for the audit row',
        }[row.proof] || 'This step has no complete Lean proof yet — click for the audit row';
        out += '<button class="lean-chip' + cls + '" data-step="' + escHtml(id) + '" title="' + title + '">' + face + '</button>';
        break;
      }
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
      return '<div class="dmath' + (no ? ' has-no' : '') + '"' + id + '>' + eqno + '<div class="dmath-scroll">' + tex2html(n.katexSrc, true) + '</div></div>';
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
    case 'quote':
      return '<blockquote class="tex-quote">' + renderNodes(n.body, ctx) + '</blockquote>';
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

/* Identifiers in Lean code that name a declaration in a cited module are
   clickable: the referenced statement expands in place, so a wrapper proof
   can be unfolded instead of read as a list of opaque names. */
let LEAN_SIG_INDEX = null;
function resolveLeanRef(tok, module, ownName) {
  const sigs = window.LEAN_SIGS || {};
  const last = tok.split('.').pop();
  if (!last || last === ownName) return null;
  if (sigs[module + '|' + last]) return module + '|' + last;
  if (!LEAN_SIG_INDEX) {
    // null prototype: decl names like `constructor` must not resolve to
    // Object.prototype members
    LEAN_SIG_INDEX = Object.create(null);
    for (const k in sigs) {
      const n = k.slice(k.indexOf('|') + 1);
      LEAN_SIG_INDEX[n] = (n in LEAN_SIG_INDEX) ? null : k;   // null = ambiguous
    }
  }
  const hit = LEAN_SIG_INDEX[last];
  return typeof hit === 'string' ? hit : null;
}

function leanCodeHtml(code, module, ownName) {
  let out = '', i = 0;
  const re = /[A-Za-z_][A-Za-z0-9_.']*/g;
  let m;
  while ((m = re.exec(code))) {
    out += escHtml(code.slice(i, m.index));
    const key = resolveLeanRef(m[0], module, ownName);
    out += key
      ? '<a class="lean-ref" data-key="' + escHtml(key) + '" title="Show this declaration">' + escHtml(m[0]) + '</a>'
      : escHtml(m[0]);
    i = m.index + m[0].length;
  }
  return out + escHtml(code.slice(i));
}

/* One chip for one step, however many declarations back it.  The face
   carries the count and the tooltip carries the names, so the reader can
   tell two neighbouring chips apart without opening either. */
function leanChipHtml(run) {
  const names = run.map(r => (r.decl || '').replace(/^GroupApproximation\./, ''));
  const face = run.length > 1
    ? 'Lean&thinsp;✓&#8202;<span class="lean-chip-n">' + run.length + '</span>'
    : 'Lean&thinsp;✓';
  const title = (run.length > 1
    ? run.length + ' Lean declarations machine-check this step — ' + names.join(', ') + '. Click for the formal proofs.'
    : 'This step is machine-checked in Lean 4 by ' + names[0] + ' — click for the formal proof');
  return '<button class="lean-chip" data-lean="' + escAttr(JSON.stringify(run)) +
    '" title="' + escAttr(title) + '">' + face + '</button>';
}

function leanDeclHtml(l) {
  const decl = l.declaration || l.decl;
  const rec = (window.LEAN_SRC || {})[l.module + '|' + decl];
  const short = decl.replace(/^GroupApproximation\./, '');
  const line = rec && rec.line ? '#L' + rec.line : '';
  const link = '<a class="lean-mod" href="' + GITHUB_BLOB + escHtml(l.module) + '.lean' + line +
    '" target="_blank" rel="noopener">' + escHtml(l.module) + '.lean' + (rec && rec.line ? ':' + rec.line : '') + '</a>';
  if (!rec) return '<div class="lean-decl"><code class="lean-name">' + escHtml(short) + '</code>' + link + '</div>';
  // statement and proof as one block: a reader who opened the declaration
  // wants the whole thing, not another fold
  const code = rec.proof ? rec.sig + '\n' + rec.proof : rec.sig;
  let inner = '<pre class="lean-code">' + leanCodeHtml(code, l.module, short.split('.').pop()) + '</pre>';
  // full coverage is the default and says nothing; partial coverage gets a
  // plain-language line (not the manifest's internal phrasing)
  if (l.covers && l.covers !== 'the complete printed proposition') {
    const covers = l.covers === 'a printed conclusion of the proposition'
      ? 'covers part of the statement'
      : 'covers ' + l.covers;
    inner += '<div class="lean-covers">' + escHtml(covers) + '</div>';
  }
  if (rec.trunc) inner += '<div class="lean-trunc">shortened here — full source on GitHub</div>';
  inner += link;
  return '<details class="lean-decl"><summary><code class="lean-name">' + escHtml(short) + '</code></summary>' + inner + '</details>';
}

/* The inline Lean panel under a theorem: the manifest's correspondence
   metadata (status, object identity, covers, coverage gap) next to the
   actual Lean statement, with the Lean proof one fold deeper. */
function leanPanelHtml(claim, texLean) {
  const entries = [];
  const seen = new Set();
  if (claim) for (const l of (claim.lean || [])) { entries.push(l); seen.add(l.module + '|' + l.declaration); }
  for (const l of (texLean || [])) {
    const k = l.module + '|' + l.decl;
    if (!seen.has(k)) { entries.push(l); seen.add(k); }
  }
  if (!entries.length) return '';
  const asText = x => typeof x === 'string' ? x : JSON.stringify(x);
  // no header, no repeated boilerplate: the badge already says Lean ✓ —
  // metadata appears only when it carries real information
  let html = entries.map(leanDeclHtml).join('');
  if (claim && claim.status && claim.status !== 'exact') html += '<div class="lean-gap"><span class="meta-label">status</span>' + escHtml(claim.status) + '</div>';
  if (claim && claim.coverage_gap) html += '<div class="lean-gap"><span class="meta-label">coverage gap</span>' + escHtml(claim.coverage_gap) + '</div>';
  if (claim && (claim.extra_assumptions || []).length) {
    html += '<div class="lean-gap"><span class="meta-label">extra assumptions</span>' +
      claim.extra_assumptions.map(x => escHtml(asText(x))).join('; ') + '</div>';
  }
  if (claim && (claim.external_inputs || []).length) {
    html += '<div class="lean-gap"><span class="meta-label">external inputs</span>' +
      claim.external_inputs.map(x => escHtml(asText(x))).join('; ') + '</div>';
  }
  if (claim) html += '<div class="lean-panel-deps" data-claim="' + escHtml(claim.id) + '"></div>';
  return html;
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
  const panel = leanPanelHtml(claim, n.lean);
  let badges = '<span class="thm-tools">';
  if (panel) badges += '<button class="badge badge-lean" aria-expanded="false" title="Machine-checked in Lean 4 — click for the formal statement and proof">Lean&thinsp;✓</button>';
  badges += '</span>';
  const c = Object.assign({}, ctx, { env: n });
  const body = renderNodes(n.body, c);
  return '<section class="thm ' + style + ' thm-' + n.env + '" id="' + n.anchor + '" data-labels="' + escHtml(n.labels.join(' ')) + '">' +
    '<div class="thm-head">' + head + badges + '</div>' +
    '<div class="thm-stmt">' + body + '</div>' +
    (panel ? '<template class="lean-panel-tpl">' + panel + '</template>' : '') +
    '</section>';
}

function renderProof(n, ctx) {
  const c = Object.assign({}, ctx, { env: n });
  let body = renderNodes(n.body, c);
  const title = n.title ? renderInline(n.title, c) : 'Proof';
  // \leanverified markers placed inside this proof: the formal counterpart
  // of exactly this argument — same badge treatment as theorems, opening
  // the same drawer, so nothing sits in the manuscript text itself.
  let leanBadge = '', leanTpl = '';
  if (n.lean && n.lean.length) {
    leanTpl = '<template class="lean-panel-tpl">' + n.lean.map(leanDeclHtml).join('') + '</template>';
    // markers written inside the proof claim this argument; markers merely
    // adopted from after \end{proof} do not outrank the audited ledger, so
    // there the graded badge (addProofBadges) wins and this one stands down
    if (n.inlineLean) {
      leanBadge = '<button class="badge badge-lean" aria-expanded="false" title="Machine-checked in Lean 4 — click for the formal statement and proof">Lean&thinsp;✓</button>';
    }
  }
  // tombstone
  body += '<span class="qed" title="end of proof">∎</span>';
  return '<details class="proof"><summary><span class="proof-label">' + title + '.</span>' + leanBadge + '</summary><div class="proof-body">' + body + '</div>' + leanTpl + '</details>';
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

/* A stack of cards: hovering a link inside a card opens a nested card on
   top of it instead of replacing it.  Every mouseover decides how much of
   the stack the pointer still justifies; anything deeper closes after a
   grace period long enough to travel from a link into its card. */
const hoverStack = [];
let hoverTimer = null;

function hoverLevelOf(node) {
  for (let i = hoverStack.length - 1; i >= 0; i--) if (hoverStack[i].el.contains(node)) return i;
  return -1;
}
function hoverCloseFrom(i) {
  while (hoverStack.length > Math.max(0, i)) hoverStack.pop().el.remove();
}

function hoverHtmlFor(a) {
  if (a.classList.contains('cite')) {
    const e = BIB.byKey[a.dataset.key];
    return e ? '<div class="hc-bib">[' + escHtml(e.label) + '] ' + renderInline(e.src.replace(/\s+/g, ' '), {}) + '</div>' : null;
  }
  const rec = LABELS[a.dataset.label];
  if (!rec) return null;
  const tgt = document.getElementById(rec.anchor);
  if (!tgt) return null;
  if (tgt.classList.contains('thm')) {
    const head = tgt.querySelector('.thm-head');
    const stmt = tgt.querySelector('.thm-stmt');
    return '<div class="hc-thm"><div class="hc-head">' + head.innerHTML + '</div>' + stmt.innerHTML + '</div>';
  }
  if (tgt.classList.contains('dmath')) return '<div class="hc-eq">' + tgt.innerHTML + '</div>';
  if (tgt.tagName === 'H2' || tgt.tagName === 'H3') return '<div class="hc-sec">§ ' + tgt.innerHTML + '</div>';
  if (tgt.classList.contains('paper-fig')) return '<div class="hc-sec">Figure ' + escHtml(rec.num) + '</div>';
  return null;
}

function hoverShow(target, html) {
  const parent = hoverLevelOf(target);
  const above = hoverStack[parent + 1];
  if (above && above.trigger === target) return;   // already open for this link
  hoverCloseFrom(parent + 1);
  const el = document.createElement('div');
  el.className = 'hover-card';
  el.innerHTML = html;
  document.body.appendChild(el);
  const r = target.getBoundingClientRect();
  const cw = Math.min(560, window.innerWidth - 24);
  el.style.maxWidth = cw + 'px';
  const hw = el.offsetWidth, hh = el.offsetHeight;
  let x = Math.min(r.left, window.innerWidth - hw - 12);
  let y = r.bottom + 8;
  if (y + hh > window.innerHeight - 8) y = r.top - hh - 8;
  el.style.left = Math.max(8, x) + 'px';
  el.style.top = Math.max(8, y + window.scrollY) + 'px';
  hoverStack.push({ el, trigger: target });
}

function setupHoverPreviews(root) {
  root.addEventListener('mouseover', ev => {
    clearTimeout(hoverTimer);
    const a = ev.target.closest('.xref, .cite, .chip-ref');
    let keep = hoverLevelOf(ev.target);            // inside card k → cards 0..k stay
    if (a) {
      const html = hoverHtmlFor(a);
      if (html) { hoverShow(a, html); keep = hoverStack.length - 1; }
    }
    hoverTimer = setTimeout(() => hoverCloseFrom(keep + 1), 320);
  });
  // pointer left the document entirely
  document.addEventListener('mouseout', ev => {
    if (ev.relatedTarget === null) {
      clearTimeout(hoverTimer);
      hoverTimer = setTimeout(() => hoverCloseFrom(0), 320);
    }
  });
  // following a link inside a card dismisses the whole stack
  root.addEventListener('click', ev => {
    if (hoverLevelOf(ev.target) >= 0 && ev.target.closest('a')) hoverCloseFrom(0);
  });
  document.addEventListener('keydown', ev => { if (ev.key === 'Escape') hoverCloseFrom(0); });
}

/* ---------- the lean drawer ---------- */

function proofOwnerEl(p) {
  // the statement this proof proves: a titled "Proof of X" names it, an
  // untitled proof follows its statement directly
  const t = p.querySelector(':scope > summary a.xref');
  if (t && t.dataset.label && LABELS[t.dataset.label]) {
    const el = document.getElementById(LABELS[t.dataset.label].anchor);
    if (el && el.classList.contains('thm')) return el;
  }
  let el = p.previousElementSibling;
  while (el && !el.classList.contains('thm') && el.tagName !== 'H2') el = el.previousElementSibling;
  return el && el.classList.contains('thm') ? el : null;
}

/* Proof badges are driven by the audited proof-step ledger, never implied:
   full check only when every printed step's proof route is graded EXACT,
   a step count when the Lean development diverges from the printed route,
   and no badge at all without audited step data. */
function ledgerRowsFor(el) {
  const L = window.LEDGER || {};
  const out = [];
  for (const lab of (el.dataset.labels || '').split(' ')) if (lab && L[lab]) out.push(...L[lab]);
  return out;
}

function addProofBadges() {
  document.querySelectorAll('#paper-body details.proof').forEach(p => {
    if (p.querySelector(':scope > summary .badge-lean')) return;   // marker-backed proofs keep their own
    const owner = proofOwnerEl(p);
    const tpl = p.querySelector(':scope > .lean-panel-tpl') || (owner && owner.querySelector('.lean-panel-tpl'));
    if (!tpl) return;
    const rows = owner ? ledgerRowsFor(owner) : [];
    if (!rows.length) {
      // no audited grading, but the proof carries adopted markers of its own:
      // a plain check, from the marker rather than from the ledger
      if (!p.querySelector(':scope > .lean-panel-tpl')) return;
      const plain = document.createElement('button');
      plain.className = 'badge badge-lean';
      plain.setAttribute('aria-expanded', 'false');
      plain.innerHTML = 'Lean&thinsp;✓';
      plain.title = 'Machine-checked in Lean 4 — click for the formal statement and proof';
      p.querySelector(':scope > summary').appendChild(plain);
      return;
    }
    const exact = rows.filter(r => r.proof === 'EXACT').length;
    const b = document.createElement('button');
    b.className = 'badge badge-lean';
    b.setAttribute('aria-expanded', 'false');
    if (exact === rows.length) {
      b.innerHTML = 'Lean&thinsp;✓';
      b.title = 'Every step of this printed proof matches the Lean development exactly (audited proof-step ledger)';
    } else {
      b.classList.add('badge-lean-partial');
      b.textContent = 'Lean ' + exact + '/' + rows.length;
      b.title = exact + ' of ' + rows.length + ' printed steps match the Lean development exactly; the statement itself is fully machine-checked. Click for the step-by-step grading.';
    }
    p.querySelector(':scope > summary').appendChild(b);
  });
}

let STEP_INDEX = null;
function ledgerStep(id) {
  if (!STEP_INDEX) {
    STEP_INDEX = Object.create(null);
    const L = window.LEDGER || {};
    for (const anchor in L) for (const r of L[anchor]) STEP_INDEX[r.step] = r;
  }
  return STEP_INDEX[id] || null;
}

const GRADE_TXT = { 'EXACT': '✓ exact', 'MISMATCH': 'different route', 'MISSING': 'not formalized', 'UNDER-SPECIFIED': 'under-specified' };
// a tombstoned row is not an inferential step, so it is not graded as one
const KIND_TXT = { 'attribution': 'attribution, not a step', 'open': 'open question, not a step' };
const KIND_TITLE = {
  'attribution': 'A citation or a piece of terminology, not an inferential step — nothing here is left to formalize',
  'open': 'A remark about what remains open, not an inferential step',
};
function ledgerHtml(rows) {
  let html = '<div class="ledger-head">Printed steps, graded against Lean' +
    ' <span class="ledger-src">from the audited proof-step ledger</span></div>';
  for (const r of rows) {
    const cls = r.kind ? 'lg-note' : 'lg-' + r.proof.toLowerCase().replace(/[^a-z]/g, '');
    const decls = r.decls.map(d => {
      const short = d.replace(/^GroupApproximation\./, '').replace(/^Mathlib:/, '');
      const key = resolveLeanRef(short, '', '');
      const code = '<code class="ls-decl">' + escHtml(short) + '</code>';
      return key ? '<a class="lean-ref" data-key="' + escHtml(key) + '" title="Show this declaration">' + code + '</a>' : code;
    }).join(' ');
    const grade = r.kind ? KIND_TXT[r.kind] : (GRADE_TXT[r.proof] || escHtml(r.proof));
    const gTitle = r.kind ? ' title="' + escAttr(KIND_TITLE[r.kind]) + '"' : '';
    html += '<div class="ledger-step"><span class="ls-grade ' + cls + '"' + gTitle + '>' + grade + '</span>' +
      '<span class="ls-claim">' + escHtml(r.claim) + '</span>' +
      (decls ? '<span class="ls-decls">' + decls + '</span>' : '') + '</div>';
  }
  return html;
}
/* One fixed side panel for all formal counterparts: a badge opens it, the
   manuscript never reflows, and the declarations arrive already expanded —
   statement and proof visible with no further clicks. */

function setupLeanPanels(root) {
  const drawer = document.createElement('aside');
  drawer.className = 'lean-drawer';
  drawer.hidden = true;
  document.body.appendChild(drawer);
  let openFor = null;

  function close() {
    drawer.hidden = true;
    if (openFor) {
      const b = openFor.querySelector('.badge-lean');
      if (b) b.setAttribute('aria-expanded', 'false');
    }
    openFor = null;
  }

  root.addEventListener('click', ev => {
    if (ev.target.closest('.lean-drawer-close')) { close(); return; }
    // an identifier inside Lean code: expand the referenced declaration in place
    const ref = ev.target.closest('.lean-ref');
    if (ref) {
      ev.preventDefault();
      const host = ref.closest('pre, .ledger-step');
      if (!host) return;
      const inStep = host.classList.contains('ledger-step');
      // a step row contains its expansion; a code block puts it just after
      const existing = inStep
        ? host.querySelector(':scope > .lean-ref-card')
        : (host.nextElementSibling && host.nextElementSibling.classList.contains('lean-ref-card') ? host.nextElementSibling : null);
      if (existing) {
        const same = existing.dataset.key === ref.dataset.key;
        existing.remove();
        if (same) return;
      }
      const rec = (window.LEAN_SIGS || {})[ref.dataset.key];
      if (!rec) return;
      const mod = ref.dataset.key.split('|')[0], nm = ref.dataset.key.split('|')[1];
      const card = document.createElement('div');
      card.className = 'lean-ref-card';
      card.dataset.key = ref.dataset.key;
      card.innerHTML = '<pre class="lean-code">' + leanCodeHtml(rec.sig, mod, nm) + '</pre>' +
        '<a class="lean-mod" href="' + GITHUB_BLOB + escHtml(mod) + '.lean#L' + rec.line +
        '" target="_blank" rel="noopener">' + escHtml(mod) + '.lean:' + rec.line + '</a>';
      if (inStep) host.appendChild(card); else host.after(card);
      return;
    }
    // a cross-reference chip inside the drawer navigates the paper: get out of the way
    if (ev.target.closest('.lean-drawer') && ev.target.closest('a[href^="#"]')) { close(); return; }
    // clicking anywhere off the drawer closes it
    if (!drawer.hidden && !ev.target.closest('.lean-drawer, .badge-lean, .lean-chip')) close();
    // a positional chip in the running text: just that step
    const chip = ev.target.closest('.lean-chip');
    if (chip) {
      ev.preventDefault();
      if (openFor === chip) { close(); return; }
      close();
      const row = chip.dataset.step ? ledgerStep(chip.dataset.step) : null;
      let run = [];
      if (!row && chip.dataset.lean) {
        try { run = JSON.parse(chip.dataset.lean); } catch (e) { warn('unreadable chip payload'); }
      }
      const content = row ? ledgerHtml([row]) : run.map(leanDeclHtml).join('');
      const title = run.length > 1 ? 'This step in Lean — ' + run.length + ' declarations' : 'This step in Lean';
      drawer.innerHTML = '<div class="lean-drawer-head"><span class="lean-drawer-title">' + escHtml(title) + '</span>' +
        '<button class="lean-drawer-close" aria-label="Close">×</button></div>' + content;
      drawer.querySelectorAll('details.lean-decl').forEach(d => { d.open = true; });
      drawer.hidden = false;
      drawer.scrollTop = 0;
      openFor = chip;
      return;
    }
    const b = ev.target.closest('.badge-lean');
    if (!b) return;
    ev.preventDefault();
    const owner = b.closest('.thm, details.proof');
    let src = owner;
    let tpl = owner && owner.querySelector('.lean-panel-tpl');
    // a proof without markers of its own borrows its theorem's formalization
    if (!tpl && owner && owner.matches('details.proof')) {
      src = proofOwnerEl(owner);
      tpl = src && src.querySelector('.lean-panel-tpl');
    }
    if (!tpl) return;
    if (openFor === owner) { close(); return; }
    close();
    const nameEl = src.querySelector('.thm-name, .proof-label');
    const name = nameEl ? nameEl.textContent.replace(/\.$/, '') : 'Statement';
    drawer.innerHTML = '<div class="lean-drawer-head"><span class="lean-drawer-title">' + escHtml(name) + ' in Lean</span>' +
      '<button class="lean-drawer-close" aria-label="Close">×</button></div>' + tpl.innerHTML;
    const rows = ledgerRowsFor(src);
    if (rows.length) drawer.insertAdjacentHTML('beforeend', ledgerHtml(rows));
    drawer.querySelectorAll('details.lean-decl').forEach(d => { d.open = true; });
    const deps = drawer.querySelector('.lean-panel-deps');
    if (deps && window.__graphDeps) {
      const id = deps.dataset.claim;
      const usedBy = buildUsedBy();
      let html = '';
      if ((window.__graphDeps[id] || []).length) html += '<div class="claim-deps"><span class="meta-label">uses</span>' + window.__graphDeps[id].map(xrefClaimChip).join('') + '</div>';
      if ((usedBy[id] || []).length) html += '<div class="claim-deps"><span class="meta-label">used by</span>' + usedBy[id].map(xrefClaimChip).join('') + '</div>';
      deps.innerHTML = html;
    }
    drawer.hidden = false;
    drawer.scrollTop = 0;
    b.setAttribute('aria-expanded', 'true');
    openFor = owner;
  });
  document.addEventListener('keydown', ev => { if (ev.key === 'Escape' && !drawer.hidden) close(); });
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
  addProofBadges();
  setupHoverPreviews(document.body);
  setupLeanPanels(document.body);
  setupTabs();
  setupScrollSpy();
  setupClaimsFilter();
  setupGraphInteractions();

  // The paper body is created client-side.  On a cold deep-link load the
  // browser tries to resolve the URL fragment before this target exists, so
  // it has nothing to scroll to.  Retry the fragment jump after rendering.
  requestAnimationFrame(() => requestAnimationFrame(scrollToCurrentFragment));

  const t1 = performance.now();
  console.log('[paper] rendered in', Math.round(t1 - t0), 'ms;',
    DIAG.warnings.length, 'warnings;', DIAG.mathErrors.length, 'math errors');
  if (DIAG.mathErrors.length) console.log('[paper] math errors:', DIAG.mathErrors);
  if (DIAG.warnings.length) console.log('[paper] warnings:', DIAG.warnings.slice(0, 50));
  window.__diag = DIAG;
}

/* ---------- interactions ---------- */

function scrollToCurrentFragment() {
  if (!location.hash || location.hash === '#') return;

  const raw = location.hash.slice(1);
  let id = raw;
  try { id = decodeURIComponent(raw); } catch (_) { /* keep raw fragment */ }

  const target = document.getElementById(id);
  if (!target) return;
  revealTarget(target);

  // Deep-link landing should be immediate even though normal in-page links
  // use smooth scrolling via CSS.  scroll-margin-top on the target still
  // keeps it clear of the sticky top bar.
  const root = document.documentElement;
  const previous = root.style.scrollBehavior;
  root.style.scrollBehavior = 'auto';
  target.scrollIntoView({ block: 'start' });
  root.style.scrollBehavior = previous;
}

function revealTarget(tgt) {
  // a link target may sit inside a collapsed proof (or Lean fold)
  for (let el = tgt; el; el = el.parentElement) {
    if (el.tagName === 'DETAILS' && !el.open) el.open = true;
  }
}

function setupTabs() {
  const tabs = [...document.querySelectorAll('.tab')].filter(t => t.dataset.view);
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
    revealTarget(tgt);
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
