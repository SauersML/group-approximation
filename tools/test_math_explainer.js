'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');
const katex = require('./paper_site/katex/katex.min.js');
const macros = require('./math_macros.js');

const tex = fs.readFileSync('non_mf_groups_exist.tex', 'utf8');
const explainerScript = fs.readFileSync('tools/math_explainer.js', 'utf8');
const explainerCss = fs.readFileSync('tools/math_explainer.css', 'utf8');
global.window = { PAPER_EXPLANATION_SOURCE: tex, katex };
global.document = { readyState: 'loading', addEventListener() {} };
global.MutationObserver = function MutationObserver() {};

require('./math_explainer.js');
const api = window.__cairnMathExplainer;
assert.ok(api, 'math explainer API was not installed');

assert.doesNotMatch(explainerScript, /lastObject\.focus/,
  'closing must not refocus and immediately reopen the triggering term');
assert.match(explainerScript, /document\.activeElement === opener\) opener\.blur\(\)/,
  'outside-click dismissal must remove focus from the triggering term');
assert.match(explainerScript, /addEventListener\('mouseout',[\s\S]*?closePanel\(\)/,
  'a transient mouseover explanation must close when the pointer leaves');
assert.match(explainerScript, /addEventListener\('focusout',[\s\S]*?closePanel\(\)/,
  'a keyboard preview must close when focus leaves');
assert.match(explainerCss, /math-explainer-formula-width/,
  'whole-formula panels must size themselves to the rendered equation');
assert.doesNotMatch(explainerCss, /math-explainer-formula[\s\S]{0,120}?90rem/,
  'short whole-formula explanations must not open an almost viewport-wide panel');
assert.match(explainerScript,
  /formulaWidth[\s\S]*?getBoundingClientRect\(\)[\s\S]*?math-explainer-formula-width/,
  'long formulas must widen the panel only as far as their rendered width requires');
assert.doesNotMatch(explainerCss, /#fcfcfb|#f6f6f4/,
  'explainer surfaces must be pure white rather than off-white');

function source(object, formula) {
  return api.sourceExplanation(object, formula);
}

const declarations = api.parseSourceExplanations(tex);
const authoredDeclarations = Array.from(
  tex.matchAll(/^\s*%<webmath\s+[^>]+>\s*$/gm)
).length;
assert.equal(declarations.length, authoredDeclarations,
  'every authored explanation must remain present');
const explanationGroups = Array.from(new Set(declarations.map(d => d.group)));
assert.deepEqual(explanationGroups,
  Array.from({ length: explanationGroups.length }, (_, index) => index),
  'contextual explanation groups must be consecutive');
for (const declaration of declarations) {
  assert.ok(declaration.object);
  assert.ok(declaration.when);
  assert.ok(Number.isInteger(declaration.group));
  assert.ok(declaration.name);
  assert.ok(declaration.explanation.length >= 250,
    `${declaration.name} needs a self-contained explanation`);
  for (const match of declaration.explanation.matchAll(/\[\[([^|\]]+)/g)) {
    assert.ok(api.explainTerm(match[1]),
      `${declaration.name} links missing glossary term ${match[1]}`);
  }
  for (const match of declaration.explanation.matchAll(/\\\(([\s\S]*?)\\\)/g)) {
    const node = { innerHTML: '' };
    api.renderTex(node, match[1]);
    assert.match(node.innerHTML, /class="katex"/,
      `${declaration.name} contains invalid inline explanation math`);
  }
}

const corona = source('Qd', '\\mathcal Q_{\\mathbf d}');
assert.equal(corona.name,
  'the matrix sequence world used to test MF');
assert.equal(corona.tex, '\\mathcal Q_{\\mathbf d}');
assert.match(corona.explanation,
  /bounded sequence\|bounded sequences.*operator norm/);
assert.match(corona.explanation, /\\\(\\mathbf d=.*\\\)/,
  'math inside source explanations must be marked for KaTeX rendering');
const coronaHtml = katex.renderToString(corona.tex, { throwOnError: true });
assert.match(coronaHtml, /mathcal/);
assert.match(coronaHtml, /msupsub/,
  'the explainer formula must preserve the source subscript');
const formulaNode = { innerHTML: '' };
api.renderTex(formulaNode, corona.tex);
assert.match(formulaNode.innerHTML, /class="katex"/,
  'the card must contain rendered KaTeX rather than the TeX source as text');
assert.match(formulaNode.innerHTML, /msupsub/,
  'the rendered card must preserve the bold sequence subscript');
assert.ok(formulaNode.innerHTML.startsWith('<span class="katex">'),
  'the card must replace the raw TeX with KaTeX markup');
const inlineSource = /\\\(([\s\S]*?)\\\)/.exec(corona.explanation);
assert.ok(inlineSource, 'the explanation must carry its notation as TeX');
const inlineNode = { innerHTML: '' };
api.renderTex(inlineNode, inlineSource[1]);
assert.match(inlineNode.innerHTML, /class="mord mathbf/,
  'bold d in the explanation must be typeset as mathematics');
assert.match(inlineNode.innerHTML, /msub/,
  'the matrix-size sequence in the explanation must preserve its subscripts');
assert.equal(source('Mdn', 'M_{d_n}(\\C)').name,
  'the square matrices used at stage n');
assert.equal(source('RadMF', '\\Rad_{\\mathrm{MF}}(G)').name,
  'the elements of G that every allowed matrix model erases');
assert.equal(source('RadMF', '\\Rad_{\\mathrm{MF}}(H)=H').name,
  'why every allowed map erases all of H');
assert.match(source('LF2', 'L_{\\F_2}(1,2)').explanation,
  /free module.*rule for copying itself/);
assert.match(source('d', 'd=e_{02}(q)').explanation,
  /row 0, column 2.*normal closure/);
assert.equal(source('πQ', '\\pi_Q\\colon W_Q\\longrightarrow Q').name,
  'the map that discards B and A and keeps Q');
assert.equal(source('∗A', 'W_Q=B*_A(Q\\times A)').name,
  'the operation that joins the two groups along A');

const qGroup = declarations.find(d => d.object === 'Qd').group;
assert.equal(declarations.find(d => d.object === 'Mdn').group, qGroup,
  'annotations immediately before one formula must share a source group');
const fadingSequences = declarations.find(
  d => d.name === 'the matrix sequences that fade to zero');
assert.notEqual(fadingSequences.group, qGroup);
assert.match(fadingSequences.explanation,
  /need not ever equal the zero matrix.*difference.*approaches zero/s,
  'the direct-sum equation needs a whole-equation translation, not only syntax');

for (const syntax of ['=', '(', ')', '[', ']', '{', '}', '⟨', '⟩', '‖', ',', '.']) {
  assert.equal(source(syntax, 'f(x)=x'), null,
    `${syntax} must not be clickable without an explicit TeX declaration`);
}
for (const unknown of ['π', 'x', 'Y', 'n', 'i', 'j', 'G']) {
  assert.equal(source(unknown, 'x+y=z'), null,
    `${unknown} must not receive an inferred explanation`);
}

for (const [symbol, name] of [
  ['=', 'equals sign'], ['∈', 'belongs to'], ['≤', 'subgroup containment'],
  ['∩', 'intersection sign'], ['⊕', 'direct-sum sign'], ['G', 'the group G'],
  ['π', 'the map pi'], ['7', 'the number 7']
]) {
  assert.equal(api.notationExplanation(symbol).name, name,
    `${symbol} needs a high-school-level notation explanation`);
}
assert.equal(api.notationExplanation('?'), null,
  'unknown notation must not receive a vague fallback explanation');

const coveredFormulas = [
  String.raw`H=\EL_{12}(L_{\F_2}(1,2)).`,
  String.raw`\mathcal Q_{\mathbf d}=\prod_nM_{d_n}(\C)\big/\bigoplus_nM_{d_n}(\C).`,
  String.raw`\bigoplus_nM_{d_n}(\C)=\{(x_n)\in\prod_nM_{d_n}(\C):\opnorm{x_n}\longrightarrow0\}`,
  String.raw`\Rad_{\mathrm{MF}}(G)=\bigcap_{\mathbf d}\bigcap_{\pi\colon G\to\U(\mathcal Q_{\mathbf d})}\ker\pi.`,
  String.raw`\operatorname{cl}_{\mathrm{MF}}^G(N)=\bigcap\{\ker f:N\le\ker f,\ f\colon G\to M,\ M\text{ MF}\}.`,
  String.raw`G/N\text{ is MF}\quad\Longleftrightarrow\quad\operatorname{cl}_{\mathrm{MF}}^G(N)=N\qquad(N\trianglelefteq G).`,
  String.raw`\operatorname{Comp}_G(L)=\{u\in G:uLu^{-1}\le L\}`,
  String.raw`\mathfrak D_G(L)=\normal{[ucu^{-1},\ell]:u\in\operatorname{Comp}_G(L),\ c\in C_G(L),\ \ell\in L}_G.`,
  String.raw`K\le\Rad_{\mathrm{MF}}(G).`,
  String.raw`L_{\F_2}(1,2)`,
  String.raw`t_i s_j=\delta_{ij},\qquad s_0t_0+s_1t_1=1.`,
  String.raw`e_{ij}(a)=1+aE_{ij}`,
  String.raw`H=\EL_{12}(R)`,
  String.raw`\Rad_{\mathrm{MF}}(H)=H.`,
  String.raw`\tau L\tau^{-1}\le L`,
  String.raw`d=e_{02}(s_1t_1).`,
  String.raw`W_Q=B*_A(Q\times A).`,
  String.raw`\Rad_{\mathrm{MF}}(W_Q)=\pi_Q^{-1}\bigl(\Rad_{\mathrm{MF}}(Q)\bigr).`,
  String.raw`\Rad_{\mathrm{MF}}(W_Q)=\ker\pi_Q=\normal{d}_{W_Q}.`,
  String.raw`\operatorname{Hom}(Q,M)\longrightarrow\operatorname{Hom}(W_Q,M)`,
  String.raw`\rho(u)\rho(L)'\rho(u)^{-1}=\rho(L)',`,
  String.raw`\rho([ucu^{-1},\ell])=1\qquad(\ell\in L).`,
  String.raw`\rho(h)\rho(u)^{-1}x\rho(u)=\rho(u)^{-1}\rho(h')x\rho(u)=\rho(u)^{-1}x\rho(h')\rho(u)=\rho(u)^{-1}x\rho(u)\rho(h).`,
  String.raw`\hsnorm{a}=\tr_d(a^*a)^{1/2},\qquad\tr_d=\frac1d\operatorname{Tr}.`,
  String.raw`\opnorm{V_n(gh)-V_n(g)V_n(h)}\longrightarrow0\qquad(g,h\in G).`,
  String.raw`K_2(V)=\{g\in G:\hsnorm{V_n(g)-1}\longrightarrow0\}.`,
  String.raw`R_{\infty\to2}(G)=\bigcap_V K_2(V),`,
  String.raw`\mathcal C_2(V,L)=\left\{(x_n)\ \middle|\sup_n\opnorm{x_n}<\infty,\ \hsnorm{[V_n(\ell),x_n]}\longrightarrow0\ (\ell\in L)\right\}`,
  String.raw`\prod_nM_{m_n}(\C)\big/\bigoplus_nM_{m_n}(\C)`,
  String.raw`U\pi(L)U^*\subseteq\pi(L),`,
  String.raw`U^*PU\le P.`,
  String.raw`\pi(\ell)U^*\xi=U^*\bigl(U\pi(\ell)U^*\bigr)\xi=U^*\xi,`,
  String.raw`\operatorname{Ad}(V(u))\bigl(\mathcal C_2(V,L)\bigr)=\mathcal C_2(V,L).`,
  String.raw`\opnorm{\operatorname{Ad}(A)-\operatorname{Ad}(B)}\le2\opnorm{A-B},`,
  String.raw`\mathcal B=\prod_nB(M_{d_n}(\C))\big/\bigoplus_nB(M_{d_n}(\C)).`,
  String.raw`[ucu^{-1},\ell]\in R_{\infty\to2}(G)\qquad(\ell\in L).`,
  String.raw`\opnorm{V_n(u)V_n(c)V_n(u)^*-V_n(ucu^{-1})}\longrightarrow0.`,
  String.raw`\hsnorm{V_n([ucu^{-1},\ell])-1}\longrightarrow0\qquad(\ell\in L).`,
  String.raw`W_n\colon G\longrightarrow\U(q_nM_{d_n}(\C)q_n)`,
  String.raw`\opnorm{q_nU_n(g)-U_n(g)q_n}\longrightarrow0\qquad(g\in G).`,
  String.raw`\opnorm{W_n(g)-q_nU_n(g)q_n}\longrightarrow0.`,
  String.raw`K\le\Rad_{\mathrm{MF}}(G).`,
  String.raw`\Theta(g)p\Theta(g)^*=p\qquad(g\in G).`,
  String.raw`b=\frac1{|S|}\sum_{s\in S}(q\Theta(s)q-q)^*(q\Theta(s)q-q)`,
  String.raw`b\ge\frac{\kappa^2}{|S|}\,q.`,
  String.raw`b_n=\frac1{|S|}\sum_{s\in S}(W_n(s)-q_n)^*(W_n(s)-q_n)`,
  String.raw`\frac1{|S|}\sum_{s\in S}\hsnorm{W_n(s)-q_n}^{\,2}\ge\frac{\kappa^2}{|S|}-o(1).`,
  String.raw`[ucu^{-1},\ell]\in R_{\infty\to2}(G).`,
  String.raw`\mathfrak D_G(L)\le R_{\infty\to2}(G).`,
  String.raw`f(D)\le\mathfrak D_{f(G)}(f(L)).`,
  String.raw`\Rad_{\mathrm{MF}}(G)=G.`,
  String.raw`\mathfrak D_Q(f(L))=Q.`,
  String.raw`\Rad_{\mathrm{MF}}(Q)=Q.`,
  String.raw`p=s_0t_0,\qquad q=s_1t_1.`,
  String.raw`p+q=1,\qquad t_1qs_1=1.`,
  String.raw`\Psi(A)=qI_3+s_0A t_0.`,
  String.raw`X=\begin{pmatrix}s_0I_3&s_1t_0I_3\\0&t_1I_3\end{pmatrix},\qquad Y=\begin{pmatrix}t_0I_3&0\\s_0t_1I_3&s_1I_3\end{pmatrix}.`,
  String.raw`\tau=\operatorname{diag}(X,Y)\in\GL_{12}(R).`,
  String.raw`\tau\,\operatorname{diag}(A,I_9)\,\tau^{-1}=\operatorname{diag}(\Psi(A),I_9).`,
  String.raw`\operatorname{diag}(X,X^{-1})=\begin{pmatrix}I&X\\0&I\end{pmatrix}\begin{pmatrix}I&0\\-X^{-1}&I\end{pmatrix}\begin{pmatrix}I&X\\0&I\end{pmatrix}\begin{pmatrix}I&0\\I&I\end{pmatrix}\begin{pmatrix}I&-I\\0&I\end{pmatrix}\begin{pmatrix}I&0\\I&I\end{pmatrix}.`,
  String.raw`L=\EL_3(R)\le H`,
  String.raw`\tau L\tau^{-1}\le L.`,
  String.raw`axb=1.`,
  String.raw`[e_{ij}(x),e_{jk}(b)]=e_{ik}(xb),\qquad[e_{ji}(a),e_{ik}(xb)]=e_{jk}(1),`,
  String.raw`[e_{wu}(r),e_{uv}(1)]=e_{wv}(r),\qquad[e_{uv}(1),e_{vw}(r)]=e_{uw}(r)`,
  String.raw`arb=0,\qquad bsar\ne0.`,
  String.raw`c_r\,r\,d_r=1,\quad e_d\,d_r\,f_d=1,\quad e_s\,s\,f_s=1,\quad e_t(c_r r)f_t=1,`,
  String.raw`a=f_s x e_t c_r,\qquad b=d_r f_d y e_s.`,
  String.raw`[g,e_{ij}(a)]=e_{ij}(y-a)\in N`,
  String.raw`A=gE_{i\ell}g^{-1},\qquad B=E_{i\ell}.`,
  String.raw`[g e_{i\ell}(1)g^{-1},e_{i\ell}(1)]=1-BA`,
  String.raw`A=g(aE_{i\ell})g^{-1},\qquad B=bE_{i\ell}.`,
  String.raw`[g e_{i\ell}(a)g^{-1},e_{i\ell}(b)]=1-BA\in N.`,
  String.raw`[1+v,e_{mn}(1)]=e_{in}(v_{im})\in N.`,
  String.raw`c=e_{34}(1),\qquad \ell=e_{12}(1),\qquad d=[\tau c\tau^{-1},\ell]`,
  String.raw`c\in C_H(L),\qquad d=e_{02}(q)\ne1,\qquad \normal d_H=H.`,
  String.raw`\tau c\tau^{-1}=e_{01}(q)e_{34}(1).`,
  String.raw`\Rad_{\mathrm{MF}}(G)=f^{-1}\!\bigl(\Rad_{\mathrm{MF}}(Q)\bigr).`,
  String.raw`\operatorname{cl}_{\mathrm{MF}}^G(N)=f^{-1}\!\left(\operatorname{cl}_{\mathrm{MF}}^Q(f(N))\right).`,
  String.raw`G/N\text{ is MF}\quad\Longleftrightarrow\quad\ker f\le N\ \text{ and }\ Q/f(N)\text{ is MF}.`,
  String.raw`\operatorname{cl}_{\mathrm{MF}}^G(N)=f^{-1}(f(N))=N.`,
  String.raw`G/\Rad_{\mathrm{MF}}(G)\cong Q/\Rad_{\mathrm{MF}}(Q).`,
  String.raw`W_Q=B*_A(Q\times A),`,
  String.raw`\pi_Q\colon W_Q\longrightarrow Q.`,
  String.raw`\operatorname{Hom}(Q,T)\longrightarrow\operatorname{Hom}(W_Q,T).`,
  String.raw`\ker\pi_Q=\normal d_{W_Q}.`,
  String.raw`f(q,a)=f(q,1)f(1,a)=f(q,1).`,
  String.raw`\Rad_{\mathrm{MF}}(W_Q)=\pi_Q^{-1}\bigl(\Rad_{\mathrm{MF}}(Q)\bigr).`,
  String.raw`\Rad_{\mathrm{MF}}(W_Q)=\ker\pi_Q=\normal d_{W_Q}.`,
  String.raw`\operatorname{cl}_{\mathrm{MF}}^{W_Q}(N)=\pi_Q^{-1}\!\left(\operatorname{cl}_{\mathrm{MF}}^Q(\pi_Q(N))\right).`,
  String.raw`W_Q/N\text{ is MF}\quad\Longleftrightarrow\quad\ker\pi_Q\le N\text{ and }Q/\pi_Q(N)\text{ is MF}.`,
  String.raw`W_{\mathbb Z}/N\text{ is MF}\quad\Longleftrightarrow\quad d\in N.`
];

function treeText(node) {
  if (node.text != null) return node.text;
  return (node.children || []).map(treeText).join('');
}

function notationTokens(node, result = []) {
  const classes = node.classes || [];
  if (classes.some(name => ['mord', 'mop', 'mbin', 'mrel', 'mopen', 'mclose', 'mpunct'].includes(name))) {
    const value = treeText(node).replace(/[\u200b\s]+/g, '').trim();
    if (value) result.push(value);
  }
  for (const child of node.children || []) notationTokens(child, result);
  return result;
}

assert.equal(coveredFormulas.length, 92);
const rootExplanations = declarations.map(declaration => declaration.explanation);
rootExplanations.push(tex);
for (let group = 0; group < coveredFormulas.length; group++) {
  const formula = coveredFormulas[group];
  const candidates = declarations.filter(declaration => declaration.group === group);
  const tree = katex.__renderToHTMLTree(formula, {
    macros: Object.assign({}, macros), displayMode: true, strict: false
  });
  const unexplained = [];
  for (const token of [...new Set(notationTokens(tree))]) {
    const info = api.sourceExplanation(token, formula, candidates) ||
      api.notationExplanation(token, formula);
    if (!info) unexplained.push(token);
    else rootExplanations.push(info.explanation);
  }
  assert.deepEqual(unexplained, [],
    `formula group ${group} contains unexplained notation: ${unexplained.join(', ')}`);
}

const glossary = api.glossaryEntries();
const glossaryByTerm = new Map(glossary.map(item => [item.term, item]));
assert.ok(glossary.length >= 100,
  'the explainer needs a foundational glossary, not only paper-specific jargon');
for (const item of glossary) {
  assert.equal(item.name, item.term, item.term + ' must use its familiar name');
  assert.ok(item.explanation.length >= 45,
    item.term + ' needs more than a circular label');
  for (const match of item.explanation.matchAll(/\[\[([^|\]]+)/g)) {
    assert.ok(glossaryByTerm.has(match[1]),
      item.term + ' links missing glossary term ' + match[1]);
  }
  for (const match of item.explanation.matchAll(/\\\(([\s\S]*?)\\\)/g)) {
    const node = { innerHTML: '' };
    api.renderTex(node, match[1]);
    assert.match(node.innerHTML, /class="katex"/,
      item.term + ' contains invalid inline explanation math');
  }
}

for (const term of [
  'approximation', 'blackboard-bold letter', 'bold letter', 'calligraphic letter',
  'complex conjugate', 'coordinate', 'corona', 'countable', 'diagonal',
  'embedding', 'equation', 'finite-matrix model', 'fraktur letter', 'Greek letter',
  'invertible', 'MF', 'model', 'multiplication error', 'nonidentity', 'nonzero',
  'off-diagonal', 'ordered pair', 'precomposition', 'radical', 'rigidity',
  'subscript', 'superscript', 'symbol', 'transpose', 'variable'
]) {
  assert.ok(glossaryByTerm.has(term), term + ' needs a followable explanation');
}
assert.match(glossaryByTerm.get('MF').explanation, /matricial field/,
  'the initials MF must be expanded');
assert.doesNotMatch(glossaryByTerm.get('MF').explanation, /MF test/,
  'MF must be defined precisely rather than called an undefined test');
assert.match(glossaryByTerm.get('MF').explanation,
  /multiplication error.*operator norm.*nonidentity.*identity.*norm matrix corona/,
  'MF must state both approximation and separation requirements');
assert.doesNotMatch(glossaryByTerm.get('corona').explanation, /Sun/,
  'definitions must omit irrelevant disambiguation');
assert.match(glossaryByTerm.get('group').explanation,
  /combining any two elements.*regrouping.*identity.*inverse/,
  'group must be defined by its axioms rather than only by a moves analogy');

assert.deepEqual(
  api.termMatches(
    'A countable group is MF if it embeds in the unitary group of a norm matrix corona'
  ).map(match => [match.text, match.term]),
  [
    ['countable', 'countable'],
    ['group', 'group'],
    ['MF', 'MF'],
    ['embeds', 'embedding'],
    ['unitary group', 'unitary group'],
    ['norm matrix corona', 'norm matrix corona']
  ],
  'every specialist phrase in the opening sentence needs its own explanation'
);

const reachableTerms = new Set();
const queue = [...rootExplanations];
while (queue.length) {
  const explanation = queue.shift();
  for (const term of api.linkedTerms(explanation)) {
    if (reachableTerms.has(term)) continue;
    reachableTerms.add(term);
    queue.push(glossaryByTerm.get(term).explanation);
  }
}
const unreachableTerms = glossary
  .map(item => item.term)
  .filter(term => !reachableTerms.has(term));
assert.deepEqual(unreachableTerms, [],
  'remove or connect unused glossary terms: ' + unreachableTerms.join(', '));

assert.equal(api.explainTerm('homomorphism').name, 'homomorphism');
assert.equal(api.explainTerm('MF group').name, 'MF group');
assert.equal(api.explainTerm('set-builder notation').name, 'set-builder notation');
assert.equal(api.explainTerm('amalgamated free product').name, 'amalgamated free product');
assert.match(api.explainTerm('Leavitt algebra').explanation,
  /free module.*two copies/);

const sourceCode = fs.readFileSync(require.resolve('./math_explainer.js'), 'utf8');
assert.match(sourceCode, /parseSourceExplanations/);
assert.match(sourceCode, /math-formula-help/);
assert.match(sourceCode, /math-term-help/);
assert.match(sourceCode, /mouseover/,
  'paper vocabulary must reveal explanations on mouseover');

console.log(`math explainer: ${declarations.length} in-place TeX explanations passed`);
