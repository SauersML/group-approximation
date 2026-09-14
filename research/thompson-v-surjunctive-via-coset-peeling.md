---
rg: 2
id: thompson-v-surjunctive-via-coset-peeling
kind: route
title: Dead - peel an automaton over V through Cantor stabilizers and finish with the coset-region lemma
target: thompson-v-surjunctive
requires: []
artifacts:
  - research/artifacts/thompson-v-coset-peeling-circularity-2026-09-12.md
---

**Dead.** Invalidated by `thompson-v-coset-stabilizers-contain-copies-of-v`.

The plan was to extend the marked-site peeling of
`rf-lamp-wreath-surjunctivity-by-marked-site-peeling` and
`finitary-split-extension-surjunctivity-proof` from lamp sites to points and
cylinders of the Cantor set:

- transplant an injective automaton over `V` to the coset spaces of pointwise
  stabilizers or rigid stabilizers, which separate finite sets;
- straighten each transplant off finitely many strata;
- finish with the coset-region lemma over a surjunctive stabilizer group.

The last step needs surjunctivity of the stabilizer group. Every such group
contains a rigid stabilizer, and rigid stabilizers are copies of `V`. The
rigid-stabilizer transplant is a map over a copy of `V` with an infinite compact
alphabet, where surjunctivity of that copy does not apply. So the step assumes
the target.
