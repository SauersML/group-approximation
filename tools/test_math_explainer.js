'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');

const tex = fs.readFileSync('non_mf_groups_exist.tex', 'utf8');
global.window = { PAPER_TEX: tex };
global.document = { readyState: 'loading', addEventListener() {} };
global.MutationObserver = function MutationObserver() {};

require('./math_explainer.js');
const api = window.__cairnMathExplainer;
assert.ok(api, 'math explainer API was not installed');

function source(object, formula) {
  return api.sourceExplanation(object, formula);
}

const declarations = api.parseSourceExplanations(tex);
assert.ok(declarations.length >= 25, 'the TeX source should carry the explanation registry');
for (const declaration of declarations) {
  assert.ok(declaration.object);
  assert.ok(declaration.when);
  assert.ok(declaration.name);
  assert.ok(declaration.explanation.length >= 80,
    `${declaration.name} needs a substantive explanation`);
}

assert.equal(source('Qd', '\\mathcal Q_{\\mathbf d}').name,
  'the norm matrix corona Q_d');
assert.match(source('Qd', '\\mathcal Q_{\\mathbf d}').explanation,
  /bounded sequences of matrices.*operator-norm difference/);
assert.equal(source('Mdn', 'M_{d_n}(\\C)').name,
  'the finite matrices used at stage n');
assert.equal(source('RadMF', '\\Rad_{\\mathrm{MF}}(G)').name,
  'the MF radical of G');
assert.equal(source('RadMF', '\\Rad_{\\mathrm{MF}}(H)=H').name,
  'the MF radical of H');
assert.match(source('LF2', 'L_{\\F_2}(1,2)').explanation,
  /split one free module into two copies.*recombine/);
assert.match(source('d', 'd=e_{02}(q)').explanation,
  /row 0, column 2.*not the identity/);
assert.equal(source('πQ', '\\pi_Q\\colon W_Q\\longrightarrow Q').name,
  'pi_Q, the quotient map from W_Q onto Q');
assert.equal(source('∗A', 'W_Q=B*_A(Q\\times A)').name,
  'joining the two groups along A');

for (const syntax of ['=', '(', ')', '[', ']', '{', '}', '⟨', '⟩', '‖', ',', '.']) {
  assert.equal(source(syntax, 'f(x)=x'), null,
    `${syntax} must not be clickable without an explicit TeX declaration`);
}
for (const unknown of ['π', 'x', 'Y', 'n', 'i', 'j', 'G']) {
  assert.equal(source(unknown, 'x+y=z'), null,
    `${unknown} must not receive an inferred explanation`);
}

assert.equal(api.explainTerm('homomorphisms').name, 'homomorphism');
assert.equal(api.explainTerm('MF groups').name, 'MF group');
assert.match(api.explainTerm('Leavitt algebra').explanation,
  /split one free module into two copies/);

const sourceCode = fs.readFileSync(require.resolve('./math_explainer.js'), 'utf8');
assert.doesNotMatch(sourceCode,
  /formulaExplanation|compoundObject|namedObject|localRole|scriptItem|scriptedTokenInfo|nearbyDefinition|grouping mark|subscript d|ambient group|measures failure|measures whether/);
assert.doesNotMatch(sourceCode, /math\.setAttribute\('tabindex'/);
assert.match(sourceCode, /parseSourceExplanations/);
assert.match(sourceCode, /math-term-help/);

console.log(`math explainer: ${declarations.length} TeX-native explanations passed`);
