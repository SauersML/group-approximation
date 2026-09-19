'use strict';

const assert = require('node:assert/strict');

global.grabGroup = (src, at) => {
  while (at < src.length && /\s/.test(src[at])) at++;
  if (src[at] !== '{') return null;
  let depth = 0;
  for (let i = at; i < src.length; i++) {
    if (src[i] === '\\') { i++; continue; }
    if (src[i] === '{') depth++;
    if (src[i] === '}' && --depth === 0) {
      return { content: src.slice(at + 1, i), next: i + 1 };
    }
  }
  return null;
};

const { renderInline } = require('./ui.js');

const cases = new Map([
  [String.raw`P\u{a}unescu`, 'Păunescu'],
  [String.raw`Dru\c{t}u`, 'Druţu'],
  [String.raw`Carri\'{o}n`, 'Carrión'],
  [String.raw`M\"{u}nster`, 'Münster'],
  [String.raw`\v{S}afár`, 'Šafár'],
]);

for (const [source, expected] of cases) {
  assert.equal(renderInline(source, {}), expected, source);
}

console.log(`paper-site inline accents: ${cases.size} cases passed`);
