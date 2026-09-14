---
rg: 2
id: every-group-is-surjunctive-over-binary-power-alphabets
kind: claim
title: Every group is surjunctive over every alphabet whose size is a power of two
distinct_from:
  every-group-is-binary-surjunctive: that is the two-symbol alphabet only; this is every size 2^n, which implies it by product closure, while the converse would need descent from 2^n to 2.
  gottschalk-surjunctivity-conjecture: that is every finite alphabet; this is the binary-power alphabets, which give the conjecture exactly when strictness ascends to larger alphabets.
  stable-finiteness-forces-binary-surjunctivity: that is the conditional statement for one group from stable finiteness of F_2[G]; this is the unconditional universal statement over binary-power alphabets.
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

**OPEN.** For every group `G` and every `n >= 1`, every injective cellular automaton on `A^G` with
`|A| = 2^n` is surjective.

**Place in the graph.**
- It is implied by the conjecture.
- It implies `every-group-is-binary-surjunctive` (`strict-rule-pairs-pass-to-product-alphabets`).
- It gives the conjecture through `gottschalk-via-alphabet-ascent`, if strictness ascends to larger
  alphabets.

## Attempts

- **Through Kaplansky.** It would follow from stable finiteness of `F_2[G]` for every group together with
  `stable-finiteness-forces-binary-surjunctivity`, whose route needs a formalizability claim
  (`binary-left-inverse-pairs-are-formalizable`, or `prime-field-left-inverse-pairs-are-stably-formalizable`).
  All three are open.
- **Linear binary case.** Linear rules over `F_2^n` are matrix Kaplansky pairs over `F_2[G]`. They are
  excluded exactly where `F_2[G]` is stably finite.
- **Where it stops.** Kaplansky stable finiteness over `F_2` is open for nonsofic groups, and every
  candidate counterexample host in the graph is nonsofic.
