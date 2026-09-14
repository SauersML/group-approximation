---
rg: 2
id: stw99-ii-via-coprime-uhf-absorbing-cases
kind: route
title: Settle the UCT problem one UHF-localized half at a time
target: stw99-problem-ii-nuclear-uct
requires: [coprime-uhf-stabilizations-detect-uct, uct-for-two-infinity-absorbing-nuclear-algebras, uct-for-three-infinity-absorbing-nuclear-algebras]
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

Let `A` be separable and nuclear.  `A ⊗ M_{2^∞}` is separable, nuclear and
`M_{2^∞}`-absorbing, so it satisfies the UCT by
`uct-for-two-infinity-absorbing-nuclear-algebras`; likewise `A ⊗ M_{3^∞}` by
`uct-for-three-infinity-absorbing-nuclear-algebras`.  The types `2^∞` and `3^∞`
are coprime, so (CU1) of `coprime-uhf-stabilizations-detect-uct` gives the UCT
for `A`.

The half at 2 has a further equivalent form,
`o2-z2-actions-fix-a-cartan-subalgebra`, through Barlak--Li Theorem 1.8
(route `uct-two-half-via-z2-actions-on-o2`).
