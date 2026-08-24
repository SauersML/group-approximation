'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');

global.window = {};
global.document = {
  readyState: 'loading',
  addEventListener() {},
};
global.MutationObserver = function MutationObserver() {};

require('./math_explainer.js');

const api = window.__cairnMathExplainer;
assert.ok(api, 'math explainer API was not installed');

function object(text, tex, context = '') {
  return api.explainObject(text, tex, context);
}

assert.equal(object('Qd', '\\mathcal Q_{\\mathbf d}').name,
  'the norm matrix corona Q_d');
assert.match(object('Qd', '\\mathcal Q_{\\mathbf d}').explanation,
  /whole sequence of matrix sizes/);
assert.equal(object('Mdn', 'M_{d_n}(\\C)').name, 'the n-th matrix algebra');
assert.match(object('d', 'd=e_{02}(q)').explanation,
  /nonidentity element.*e_02\(q\)/);
assert.match(object('q', 'd=e_{02}(q)').explanation, /q = s₁t₁/);
assert.equal(object('RadMF', '\\Rad_{\\mathrm{MF}}(G)').name,
  'the MF radical of G');
assert.match(object('RadMF', '\\Rad_{\\mathrm{MF}}(G)').explanation,
  /every homomorphism.*norm matrix corona/);
assert.equal(object('EL12', 'H=\\EL_{12}(R)').name,
  'the elementary group of rank 12');
assert.equal(object('e02', 'd=e_{02}(q)').name,
  'the elementary matrix e_02');
assert.equal(object('WQ', 'W_Q=B*_A(Q\\times A)').name,
  'the group W_Q built over Q');
assert.equal(object('πQ', '\\pi_Q\\colon W_Q\\longrightarrow Q').name,
  'the quotient map π_Q');
assert.equal(object('⋂d', '\\bigcap_{\\mathbf d}').name,
  'the intersection over every matrix-size sequence');
assert.equal(object('⋂π:G→U(Qd)',
  '\\bigcap_{\\pi\\colon G\\to\\U(\\mathcal Q_{\\mathbf d})}').name,
  'the intersection over every corona representation');
assert.equal(object('⨁n', '\\bigoplus_nM_{d_n}(\\C)').name,
  'the sequences that vanish');
assert.equal(object('∗A', 'B*_A(Q\\times A)').name,
  'gluing the two groups along A');
assert.equal(object('H', '\\Rad_{\\mathrm{MF}}(H)=H').name,
  'H, the group proved non-MF');
assert.equal(object('G', 'K\\trianglelefteq G').name,
  'G, the group being tested');
assert.equal(object('L', 'uLu^{-1}\\le L').name,
  'L, the subgroup compressed into itself');
assert.equal(object('N', 'N\\trianglelefteq G').name,
  'N, the subgroup being collapsed');

for (const syntax of ['(', ')', '[', ']', '{', '}', '⟨', '⟩', '‖', ',', '.']) {
  assert.equal(object(syntax, 'f(x)=x'), null, `${syntax} must not be clickable`);
}
for (const unknown of ['x', 'Y', 'n', 'i', 'j']) {
  assert.equal(object(unknown, 'x+y=z'), null,
    `${unknown} must not receive a generic explanation`);
}
assert.equal(object('π', '\\pi(x)=y'), null,
  'a map symbol without an actual displayed source and target is not annotated');
assert.match(object('π',
  '\\bigcap_{\\pi\\colon G\\to\\U(\\mathcal Q_{\\mathbf d})}\\ker\\pi').explanation,
  /any homomorphism from G/);

assert.match(api.explainFormula(
  '\\mathcal Q_{\\mathbf d}=\\prod_nM_{d_n}(\\C)\\big/\\bigoplus_nM_{d_n}(\\C)'),
  /bounded sequence.*operator-norm difference/i);
assert.match(api.explainFormula('\\Rad_{\\mathrm{MF}}(H)=H'),
  /every homomorphism.*every MF group/i);
assert.match(api.explainFormula('uLu^{-1}\\le L'), /one-sided self-compression/);
assert.match(api.explainFormula('d=e_{02}(q)'), /q is nonzero.*not the identity/i);
assert.equal(api.explainFormula('x=y'), '');

assert.equal(api.explainTerm('homomorphisms').name, 'homomorphism');
assert.equal(api.explainTerm('MF groups').name, 'MF group');

const source = fs.readFileSync(require.resolve('./math_explainer.js'), 'utf8');
assert.doesNotMatch(source,
  /Plain-language math|What it means here|How to read the formula|In this sentence|grouping mark|subscript d|ambient group/);
assert.doesNotMatch(source, /math\.setAttribute\('tabindex'/);
assert.match(source, /math-term-help/);
assert.match(source, /openTerm/);

console.log('math explainer: contextual object explanations passed');
