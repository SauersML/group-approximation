'use strict';

const assert = require('node:assert/strict');
const katex = require('./paper_site/katex/katex.min.js');
const macros = require('./math_macros.js');

const cases = [
  ['\\Rad_{\\mathrm{MF}}(G)', 'Rad'],
  ['\\normal{d}_G', 'd'],
  ['\\EL_{12}(\\F_2)', 'EL'],
  ['\\opnorm{x_n}\\longrightarrow0', 'x']
];

for (const [source, visible] of cases) {
  const html = katex.renderToString(source, {
    macros: Object.assign({}, macros),
    throwOnError: true,
    strict: false,
    output: 'html'
  });
  assert.match(html, new RegExp(visible));
  assert.doesNotMatch(html, /katex-error|\\(?:Rad|normal|EL|F|opnorm)\b/);
}

console.log(`math macros: ${cases.length} manuscript formulas rendered`);
