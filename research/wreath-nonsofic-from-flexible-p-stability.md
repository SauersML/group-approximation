---
rg: 2
id: wreath-nonsofic-from-flexible-p-stability
kind: route
title: Flexible P-stability, centralizer rounding and permutation co-density make the summit wreath nonsofic
target: arithmetic-coset-wreath-is-not-sofic
requires:
  - sl3-z-inverse-3-is-flexibly-p-stable
  - kazhdan-almost-centralizers-round-in-finite-actions
  - arithmetic-finite-actions-are-lambda-generated
---

Full derivation:
`research/artifacts/wreath-permutation-collapse-2026-08-22.md`
(Theorem P).  Chain: a sofic approximation of `W_3` restricts to an
almost-action of `Gamma`; flexible P-stability corrects it to genuine
finite actions (vanishing padding); the base lamp almost-commutes with
the corrected `Lambda`-action, so the rounding theorem replaces it by
an exactly `Lambda`-equivariant permutation `c`; permutation
co-density upgrades `c` to `Gamma`-equivariance, so conjugating by
`tau(h)` fixes `c`; hence the sofic image of the nontrivial element
`k_0 . h k_0 h^{-1}` is Hamming-near `c^2`, which is near the identity
since `k_0^2 = e` and equivariant permutations act freely per orbit —
fixed-point density near 1, contradicting soficity's requirement of
density near 0 on nontrivial elements.

This is the wreath permutation-twin of the HNN theorem
(`hnn-over-codense-kazhdan-subgroup-not-hyperlinear`): flexible
P-stability replaces flexible HS-stability, the rounding theorem
replaces the (T;FD) conjugation gap, permutation co-density replaces
finite-dimensional co-density — and no compression or infranormality
is used anywhere, so it lives exactly where
`arithmetic-integral-subgroup-is-incompressible` says Kun–Thom cannot
go.  One hole remains: the flexible P-stability of `Gamma` itself.

**SL_2 scope extension.**  The identical chain runs for
`(SL_2(Z[1/p]), SL_2(Z))`: Serre's congruence subgroup property for
`SL_2(Z[1/p])` (infinitely many units) plus the Margulis normal
subgroup theorem (irreducible lattice in a rank-two product) make every
finite action congruence, so the rounding theorem needs its uniform gap
only on congruence representations, where Selberg's property (tau) of
`SL_2(Z)` replaces property (T).  Hence flexible P-stability of
`SL_2(Z[1/2])` implies ITS coset wreath is not sofic — the wreath
sibling of `hnn-over-sl2-z-not-sofic-if-sl2-z-inverse-p-p-stable`,
conditional on the same permutation-DV hole.
