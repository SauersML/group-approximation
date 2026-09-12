---
rg: 2
id: every-group-has-positive-rokhlin-entropy-action
kind: claim
title: Every countably infinite group has a free ergodic p.m.p. action of positive Rokhlin entropy
root: true
distinct_from:
  gottschalk-surjunctivity-conjecture: that is surjunctivity of cellular automata; this is an entropy existence statement from which Seward's Krieger II derives surjunctivity, with no converse known.
  bernoulli-shift-entropy-classifies-for-every-group: that is the classification of Bernoulli shifts by base entropy; this is the positive-entropy hypothesis from which Seward derives the equality of Bernoulli Rokhlin entropy with base entropy.
---

**OPEN.** Every countably infinite group `G` admits a free ergodic
probability-measure-preserving action with positive Rokhlin entropy.

**Source.** B. Seward, *Krieger's finite generator theorem for actions of
countable groups II*, arXiv:1501.03367. The abstract, read on 2026-09-12:
"Under the assumption that every countable group admits a free ergodic action
of positive Rokhlin entropy, we prove that: (i) the Rokhlin entropy of a
Bernoulli shift is equal to the Shannon entropy of its base; (ii) Bernoulli
shifts have completely positive Rokhlin entropy; and (iii) Gottschalk's
surjunctivity conjecture and Kaplansky's direct finiteness conjecture are
true."

**Why it is a root.** One statement implies:
- `gottschalk-surjunctivity-conjecture`;
- Kaplansky direct finiteness, whose counterexample side is
  `leavitt-unit-group-algebra-not-directly-finite`;
- `bernoulli-shift-entropy-classifies-for-every-group`.

It can only fail on nonsofic groups. Seward, arXiv:1805.08279, introduction:
"The Rokhlin entropy of the Bernoulli shift G↷(L^G,λ^G) is H(L,λ) when G is
sofic but when G is not sofic its value is not yet known." The nonsofic groups
this graph builds (`openai-leavitt-unit-nonsofic`, the Kun--Thom groups) are
therefore the first live test cases.

**Not wired.** The implication routes need the per-group form of Seward's
theorems (Section 1 of arXiv:1501.03367), which has not been read here. No
route targets or consumes this claim until that is done.

## Attempts

- None run. The strategy lane `opportunity-mapper` opened this claim as a
  target that no lane covers; see item 1 of
  `research/artifacts/opportunity-map-2026-09-12.md`. The first step recorded
  there is to read the per-group statements of Seward II, then to test strict
  compression over a Kazhdan pair against generating partitions of free
  actions of `L_(F_2)(1,2)^×`.
- Factor maps carry no information on these groups. Bowen, arXiv:0812.2718,
  abstract: "if G is a countable group that contains a nonabelian free
  subgroup then every pair of nontrivial Bernoulli shifts over G are weakly
  isomorphic."
