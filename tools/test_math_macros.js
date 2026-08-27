'use strict';

const assert = require('node:assert/strict');
const katex = require('./paper_site/katex/katex.min.js');
const macros = require('./math_macros.js');
const normalize = require('./math_normalize.js');

const cases = [
  ['\\Rad_{\\mathrm{MF}}(G)', 'Rad'],
  ['\\normal{d}_G', 'd'],
  ['\\EL_{12}(\\F_2)', 'EL'],
  ['\\opnorm{x_n}\\longrightarrow0', 'x']
];

// mathtools environments the manuscripts use and KaTeX lacks; the site
// normalizes them before rendering (tools/math_normalize.js)
cases.push(
  ['\\begin{psmallmatrix}I&B\\\\0&I\\end{psmallmatrix}', 'B'],
  ['\\begin{bsmallmatrix}1&0\\\\B&1\\end{bsmallmatrix}', 'B'],
  ['\\begin{pmatrix*}[r]-1&2\\\\3&-4\\end{pmatrix*}', '4']
);

for (const [rawSource, visible] of cases) {
  const source = normalize(rawSource);
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

// the paper-site parser must not split a paragraph at an environment that
// sits inside inline math (the 2026-08-27 psmallmatrix rendering defect)
global.grabGroup = global.grabGroup || ((src, at) => {
  while (at < src.length && /\s/.test(src[at])) at++;
  if (src[at] !== '{') return null;
  let depth = 0;
  for (let i = at; i < src.length; i++) {
    if (src[i] === '\\') { i++; continue; }
    if (src[i] === '{') depth++;
    if (src[i] === '}' && --depth === 0) return { content: src.slice(at + 1, i), next: i + 1 };
  }
  return null;
});
const { parseBlocks, DIAG } = require('./paper_site/parser.js');
const para = 'matrices $\\begin{psmallmatrix}I&B\\\\0&I\\end{psmallmatrix}$ and $\\begin{psmallmatrix}I&0\\\\B&I\\end{psmallmatrix}$ with $B\\in M_6(R)$.';
const before = DIAG.warnings.length;
const nodes = parseBlocks(para, { fig: 0, stepEq() { return 1; }, stepThm() { return 1; }, stepMain() { return 'A'; }, stepSection() { return 1; }, stepSub() { return 1; }, section: 1 });
assert.equal(nodes.length, 1, 'one paragraph node');
assert.equal(nodes[0].src, para, 'paragraph text kept intact');
assert.equal(DIAG.warnings.length, before, 'no unknown-environment warning');
console.log('paper-site parser: inline-math environments left to KaTeX');
