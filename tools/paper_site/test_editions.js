'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');

const here = __dirname;
const repo = path.resolve(here, '..', '..');
const parser = fs.readFileSync(path.join(here, 'parser.js'), 'utf8');
const paper = fs.readFileSync(path.join(repo, 'non_mf_groups_exist.tex'), 'utf8');
const notes = fs.readFileSync(path.join(repo, 'non_mf_group_notes.tex'), 'utf8');

const result = vm.runInNewContext(parser + String.raw`
parsePaper(PAPER);
const external = {};
for (const [label, rec] of Object.entries(LABELS)) {
  external['paper-' + label] = Object.assign({}, rec, {
    href: '../paper/#' + rec.anchor,
  });
  delete LABELS[label];
}
Object.assign(LABELS, external);
parsePaper(NOTES);
const refs = [...NOTES.matchAll(/\\(?:eqref|ref)\{([^}]*)\}/g)].map(match => match[1]);
({
  referenceCount: new Set(refs).size,
  missing: [...new Set(refs.filter(label => !LABELS[label]))],
  theoremAHref: LABELS['paper-thm:A'] && LABELS['paper-thm:A'].href,
});
`, {PAPER: paper, NOTES: notes, console});

assert.equal(result.missing.length, 0, result.missing.join(', '));
assert.match(result.theoremAHref, /^\.\.\/paper\/#/);
console.log(`paper-site editions: ${result.referenceCount} notes labels resolved`);
