---
rg: 2
id: subshift-elementary-group-is-simple-modulo-centre
kind: claim
title: EL_3 over a minimal subshift algebra is simple modulo its finite centre and has no finite quotients
distinct_from:
  binary-leavitt-elementary-group-is-simple: that detects roots over the purely infinite binary Leavitt algebra using strong two-sided division; this detects roots over a stably finite ring with no such division, using tower subrings over small cylinders.
artifacts:
  - research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md
---

Let `R = LC(X,F_q) ⋊ Z` be as in `minimal-subshift-algebra-is-simple-lef-ring`, and
`G = EL_3(R)`. Then every normal subgroup of `G` is either contained in the centre
`Z(G) ⊆ F_q^x I_3` or equal to `G`. Consequently:

- `G/Z(G)` is an infinite, finitely generated, simple group;
- `G` has no nontrivial finite quotient.

The mechanism is root detection through tower subrings. Let `U` be a clopen set with long return
times. The elements `E_ab(W) = chi_(T^a W) u^(a-b)`, for `W ⊆ U` and `|a|, |b| <= m`, span a
subring `B_m(U) ≅ M_(2m+1)(LC(U,F_q))`. Products `r b r'` with `b ∈ B_m(U)` and `r, r'` of
`u`-propagation `<= w` lie in `B_(m+w)(U)`. So a commutator of a noncentral `g` with a localized
root `e_ij(s)` is a locally constant function `U -> GL_d(F_q)`, `d = 3(2m'+1)`. A noncentral value
yields an entire copy of `SL_d(F_q)` inside the normal subgroup. A scalar value yields a nonzero
root through a column leaving the tower. In both cases the level ideal is nonzero, and simplicity
of `R` finishes.
