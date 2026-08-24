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

assert.equal(api.explainToken('MF', '').name, 'MF');
assert.equal(api.explainToken('Rad', '\\Rad_{\\mathrm{MF}}(G)').name, 'MF radical');
assert.equal(api.explainToken('∈', 'x \\in G').name, 'belongs to');
assert.equal(api.explainToken('*', 'B*_D(Q \\times D)').name, 'amalgamated free product');
assert.equal(api.explainToken('C', 'C_G(L)').name, 'centralizer');
assert.equal(api.explainToken('Q', '\\mathcal Q_{\\mathbf d}').name, 'a norm matrix corona');
assert.equal(api.explainToken('e', 'e_{12}(a)').name, 'an elementary matrix');
assert.equal(api.explainToken('N', 'N\\trianglelefteq G').name, 'the normal subgroup N');
assert.equal(api.explainToken('Y', 'Y=G'), null);
assert.equal(api.explainToken('(', 'f(x)=x'), null);
assert.equal(api.explainTerm('homomorphisms').name, 'homomorphism');
assert.equal(api.explainTerm('MF groups').name, 'MF group');
assert.equal(api.scriptInfo('MF', 'Rad', 'subscript', '\\Rad_{\\mathrm{MF}}(G)').name,
  'the MF subscript');
assert.equal(api.scriptInfo('Q', 'W', 'subscript', 'W_Q').name,
  'the quotient label Q');
assert.equal(api.scriptInfo('n', 'd', 'subscript', 'd_n').name, 'the stage n');
assert.equal(api.scriptInfo('G', '⟨⟨d⟩⟩', 'subscript', '\\normal{d}_G').name,
  'the ambient-group subscript');
assert.match(api.explainFormula('\\Rad_{\\mathrm{MF}}(H)=H'),
  /every homomorphism.*every MF group/i);
assert.match(
  api.explainFormula('\\Rad_{\\mathrm{MF}}(W_Q)=\\ker\\pi_Q=\\normal{d}_{W_Q}'),
  /kernel.*normal subgroup/i);
assert.match(api.explainFormula('uLu^{-1}\\le L'), /self-compression/);
assert.match(api.localRole('H', 'H=\\operatorname{EL}_{12}(R)', ''),
  /group constructed from elementary matrices/);
assert.match(api.localRole('Q', 'W_Q=B*_D(Q\\times D)', ''),
  /quotient that remains visible/);
assert.match(api.localRole('x', 'x\\in G', 'Let x be a nonidentity element of G.'),
  /nonidentity element of G/);
assert.match(api.localRole('i', 'e_{ij}(a)', ''), /index/);
assert.match(api.localRole('G', '\\Rad_{\\mathrm{MF}}(G)=G', ''),
  /entire group under study/);
assert.equal(api.localRole('⊴', 'N\\trianglelefteq G', ''), '');

const source = fs.readFileSync(require.resolve('./math_explainer.js'), 'utf8');
assert.doesNotMatch(source,
  /Plain-language math|What it means here|How to read the formula|whole-formula explanation/);
assert.match(source, /math-term-help/);
assert.match(source, /openTerm/);

console.log('math explainer: symbol and formula vocabulary passed');
