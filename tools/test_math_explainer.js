'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');
const katex = require('./paper_site/katex/katex.min.js');

const tex = fs.readFileSync('non_mf_groups_exist.tex', 'utf8');
global.window = { PAPER_EXPLANATION_SOURCE: tex, katex };
global.document = { readyState: 'loading', addEventListener() {} };
global.MutationObserver = function MutationObserver() {};

require('./math_explainer.js');
const api = window.__cairnMathExplainer;
assert.ok(api, 'math explainer API was not installed');

function source(object, formula) {
  return api.sourceExplanation(object, formula);
}

const declarations = api.parseSourceExplanations(tex);
assert.ok(declarations.length >= 25, 'the TeX source should carry in-place explanations');
for (const declaration of declarations) {
  assert.ok(declaration.object);
  assert.ok(declaration.when);
  assert.ok(Number.isInteger(declaration.group));
  assert.ok(declaration.name);
  assert.ok(declaration.explanation.length >= 80,
    `${declaration.name} needs a substantive explanation`);
}

const corona = source('Qd', '\\mathcal Q_{\\mathbf d}');
assert.equal(corona.name,
  'the norm matrix corona used in the definition of MF');
assert.equal(corona.tex, '\\mathcal Q_{\\mathbf d}');
assert.match(corona.explanation,
  /bounded sequences of matrices.*operator norm/);
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
  'the matrices in the nth finite model');
assert.equal(source('RadMF', '\\Rad_{\\mathrm{MF}}(G)').name,
  'the elements of G invisible to every finite-matrix limit');
assert.equal(source('RadMF', '\\Rad_{\\mathrm{MF}}(H)=H').name,
  'every element of H is invisible to every MF-target representation');
assert.match(source('LF2', 'L_{\\F_2}(1,2)').explanation,
  /two copies of a free module.*recover the two inputs/);
assert.match(source('d', 'd=e_{02}(q)').explanation,
  /row 0, column 2.*not the identity/);
assert.equal(source('πQ', '\\pi_Q\\colon W_Q\\longrightarrow Q').name,
  'the map that forgets the attached B and A parts and returns Q');
assert.equal(source('∗A', 'W_Q=B*_A(Q\\times A)').name,
  'joining B and Q times A along their common subgroup A');

const qGroup = declarations.find(d => d.object === 'Qd').group;
assert.equal(declarations.find(d => d.object === 'Mdn').group, qGroup,
  'annotations immediately before one formula must share a source group');
assert.notEqual(declarations.find(d => d.name === 'the sequences discarded by the quotient').group, qGroup);

for (const syntax of ['=', '(', ')', '[', ']', '{', '}', '⟨', '⟩', '‖', ',', '.']) {
  assert.equal(source(syntax, 'f(x)=x'), null,
    `${syntax} must not be clickable without an explicit TeX declaration`);
}
for (const unknown of ['π', 'x', 'Y', 'n', 'i', 'j', 'G']) {
  assert.equal(source(unknown, 'x+y=z'), null,
    `${unknown} must not receive an inferred explanation`);
}

assert.equal(api.explainTerm('homomorphism').name, 'homomorphism');
assert.equal(api.explainTerm('MF group').name, 'MF group');
assert.match(api.explainTerm('Leavitt algebra').explanation,
  /split one free module into two copies/);

const sourceCode = fs.readFileSync(require.resolve('./math_explainer.js'), 'utf8');
assert.doesNotMatch(sourceCode,
  /formulaExplanation|compoundObject|namedObject|localRole|scriptItem|scriptedTokenInfo|nearbyDefinition|grouping mark|subscript d|ambient group|measures failure|measures whether|TERM_PATTERN|ALIASES/);
assert.doesNotMatch(sourceCode, /math\.setAttribute\('tabindex'/);
assert.match(sourceCode, /parseSourceExplanations/);
assert.match(sourceCode, /math-term-help/);

console.log(`math explainer: ${declarations.length} in-place TeX explanations passed`);
