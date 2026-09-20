---
rg: 2
id: wave2-audit-cyclotomic-kazhdan-cover-proof
kind: route
title: Coinduce an integral cover of the index-seven kernel, remove the diagonal, and use its cyclotomic second homology
target: wave2-audit-ghb7-cyclotomic-kazhdan-cover
requires:
  - cckw-ghb2-kms-group-structure
  - ghb7-normal-subgroup-b2-is-orbit-euler-count
  - bdhv-central-extension-property-t
  - kazhdan-cover-models-round-iff-kernel-fixed-mass-one
artifacts:
  - research/artifacts/hyperbolic-rf-wave2-audit-2026-09-20.md
---

Sections 1--4 of the artifact give a complete proof. The rational homology
of the index-seven orbit complex identifies `H_2(K;Q)` with the augmentation
submodule of `Q[C_7]`. Its dual is the irreducible six-dimensional rational
cyclotomic representation. Thus the conjugates of every nonzero rational
class span all six dimensions.

The usual coset embedding puts `G` into `K^7 semidirect C_7`. Pull back
`E_c^7 semidirect C_7`, where `E_c` is the integral central cover, and quotient
its central diagonal `Z`. The resulting kernel is `A`. Over `K` the extension
is central and its homology transgression has full rational rank six;
the five-term sequence makes its abelianization finite. The central-cover
property-(T) theorem and finite-index permanence make the whole cover Kazhdan.

The cyclic action has no nonzero fixed vector in `A`. The seventh power of
any generator lift lies in `A` and is fixed by that lift, so it is trivial.

For the conditional models, take primitive central eigenspace representations
of finite quotients of `E_c`. Tensor one coordinate with the conjugate of its
neighbor, and induce across the cyclic permutation. The diagonal centre acts
trivially, so this gives genuine representations of the constructed cover.
Its kernel acts pointwise almost trivially, but has no fixed vectors.
The required Kazhdan-cover criterion precludes flexible rounding of the
section models of `G`. The explicit monomial action gives the claimed exact
power relators and seven-block commutator defects.
