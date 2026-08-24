'use strict';

const assert = require('node:assert/strict');

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
assert.match(api.explainFormula('\\Rad_{\\mathrm{MF}}(H)=H'), /every MF-target representation/);
assert.match(api.explainFormula('uLu^{-1}\\le L'), /self-compression/);
assert.match(api.localRole('H', 'H=\\operatorname{EL}_{12}(R)', ''),
  /group constructed from elementary matrices/);
assert.match(api.localRole('Q', 'W_Q=B*_D(Q\\times D)', ''),
  /quotient that remains visible/);
assert.match(api.localRole('x', 'x\\in G', 'Let x be a nonidentity element of G.'),
  /nonidentity element of G/);
assert.match(api.localRole('i', 'e_{ij}(a)', ''), /index/);

console.log('math explainer: symbol and formula vocabulary passed');
