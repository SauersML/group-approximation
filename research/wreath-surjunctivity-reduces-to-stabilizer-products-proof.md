---
rg: 2
id: wreath-surjunctivity-reduces-to-stabilizer-products-proof
kind: route
title: Peel marked sites keeping lamp values as group coordinates, then apply the coset-region lemma over A^U x G_U
target: wreath-surjunctivity-reduces-to-stabilizer-products
requires:
  - surjunctivity-passes-to-subgroups
artifacts:
  - research/artifacts/wreath-surjunctivity-stabilizer-products-2026-09-12.md
  - research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md
---

"Only if": `A^U x G_U` is a subgroup of `W`, and surjunctivity passes to subgroups.
"If": the marked-site peeling of the residually finite theorem, with separating
subgroups `H_S = {n : n|_S = 1}`. The coset space `H_U\W` is read as the group
`A^U x G` rather than as `G` with alphabet `B^(A^U)`. The transplanted automaton is
then a finite-memory map there, invariant under `A^U x G_U`. The coset-region lemma
needs exactly the surjunctivity of `A^U x G_U`. The full argument is in the
artifact's "If" section, steps 1–8.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 11 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).
