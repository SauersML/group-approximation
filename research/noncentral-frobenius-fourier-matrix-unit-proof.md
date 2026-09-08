---
rg: 2
id: noncentral-frobenius-fourier-matrix-unit-proof
kind: route
title: Cut the rational affine Fourier basis by one trace hyperplane and identify every surviving matrix unit
target: noncentral-frobenius-negative-corner-is-rational-matrix-algebra
requires: []
artifacts:
  - research/artifacts/noncentral-frobenius-negative-rational-matrix-corner-2026-09-08.md
---

The nondegenerate field-trace pairing gives rational Fourier
projections `p_a` for the elementary abelian translation subgroup.
Multiplier conjugation sends `p_b` to `p_(b/s)`. The negative
projection of translation by one is precisely the sum of those
`p_a` with `Tr(a)=1`.

The basis `p_a m_s` of the full rational group algebra survives
compression on both sides exactly when `a` and `as` have trace
one. The survivors are indexed without repetition by pairs in
`Omega x Omega` and are the displayed `E_(a,as)`. Direct
multiplication and inversion give the matrix-unit identities and
star operation. This proves both spanning and independence for
the whole corner, rather than only an embedding of a matrix block.

Conjugating `J` by `t_v m_s` gives `t_s`, so precisely the
translations preserve the corner. Their Fourier action is diagonal.
For an arbitrary multiplier, the domain and range of its compressed
group element are products of commuting negative translation
projections. When the multiplier is not one, two independent
trace functionals give their rank as `2^(n-2)`.

Expanding any local matrix PVM in these rational matrix units
gives its finite-support group-ring realization. This does not
claim that the independent contexts of a no-CE BCS can be glued
within the finite packet or by its literal corner normalizer.
