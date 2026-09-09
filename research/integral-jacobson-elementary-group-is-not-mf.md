---
rg: 2
id: integral-jacobson-elementary-group-is-not-mf
kind: claim
root: true
title: Elementary groups over the integral Toeplitz--Jacobson algebra are not MF
distinct_from:
  finite-additive-order-one-sided-defects-are-mf-invisible: that settles every coefficient ring in which the complementary idempotent has finite additive order, so every positive characteristic, at rank at least four; this is the characteristic-zero universal case, where that idempotent has infinite additive order and the theorem's witness is infinite cyclic.
  integral-jacobson-defect-has-no-normal-kazhdan-subgroup: that is the established exclusion of one method, the normal-Kazhdan criterion, over the integral ring; this is the open target that method was meant to reach.
  binary-jacobson-steinberg-head-root-is-mf-invisible: that is the binary Jacobson algebra in rank five, established; this is the integral algebra at every rank, open.
  jacobson-unit-group-is-locally-finite-and-mf: that is the rank-one unit group over the binary field, which is MF; this asks about elementary groups of rank at least two over the integers.
  laurent-elementary-groups-are-residually-finite: that is residual finiteness of the elementary groups over the Laurent quotient, the symbol image; this is about the extension of that image by the finitary kernel.
artifacts:
  - research/artifacts/finite-rank-compression-defect-dichotomy-2026-09-09.md
---

**OPEN.**  Let `J_Z = Z<s,t | ts = 1>`.  The claim is that `EL_n(J_Z)`
is not MF for every `n >= 2`, or at least for all large `n`.

**Why this is the test case.**  `J_Z` is the universal unital ring with a
one-sided inverse, and it is not directly finite.  The one-way ring
implication "`EL_n(R)` MF implies `R` directly finite", with no
characteristic hypothesis, is equivalent to this claim by the universal
property: every ring with `ts = 1`, `st != 1` receives `J_Z`, and
`EL_n(J_Z) -> EL_n(R)` carries the obstruction.  The converse implication
is false (`stably-finite-group-ring-with-non-mf-elementary-groups`), so
this one-way statement is all that remains of the ring equivalence.  In
positive characteristic the implication is established at `n >= 4`
(`finite-additive-order-one-sided-defects-are-mf-invisible`).

**What is known about the group.**  The symbol map
`EL_n(J_Z) -> EL_n(Z[z,z^-1])` has residually finite image
(`laurent-elementary-groups-are-residually-finite`) and a kernel of
finite-rank perturbations of the identity, which is locally residually
finite (a finitely generated subgroup lies in some `GL_N(Z)`).  So
`EL_n(J_Z)` is (locally residually finite)-by-(residually finite), the
same shape as the manuscript's non-MF group `W`, which is (locally
residually finite)-by-`Z`; the shape alone decides nothing.  Its
compression defect for `L = EL_3(J_Z)` in rank four is nontrivial and
contains infinite cyclic central subgroups and non-normal copies of
`SL_3(Z)` (`integral-jacobson-defect-has-no-normal-kazhdan-subgroup`).
The negation, that `EL_n(J_Z)` is MF, is equally open; a proof of it
would refute the characteristic-free ring implication.

**Structure of the radical (2026-09-09).**  The symbol kernel is
`GL_fin(Z)`, the relative elementary subgroup is `SL_fin(Z)`, and the
quotient `EL_n(J_Z)/SL_fin(Z)`, a central `C_2`-extension of
`EL_n(Z[z,z^-1])`, is residually finite; so
`Res_fin(EL_n(J_Z)) = SL_fin(Z)` and `Rad_MF(EL_n(J_Z)) <= SL_fin(Z)`
(`integral-jacobson-sign-quotient-is-residually-finite`).  For `n >= 4`
every MF homomorphism is injective or trivial on `SL_fin(Z)`
(`integral-jacobson-mf-radical-is-all-or-nothing`).  So this claim is
equivalent, for `n >= 4`, to: every MF homomorphism of `EL_n(J_Z)` kills
the single transvection `z = diag(1,1,1,1 + f_12)`; and its negation is
equivalent to: one MF homomorphism keeps `z` alive, necessarily with an
image of infinite order
(`central-defect-element-mf-image-is-trivial-or-infinite`).

## Attempts

- **Normal Kazhdan witness in a compression defect** (the manuscript's
  criterion, which proves every other non-MF theorem in this program).
  Dead at every rank and in every subgroup of `GL_n(J_Z)`, and for every
  homomorphic encoding: `integral-jacobson-defect-has-no-normal-kazhdan-subgroup`
  shows every finitely generated normal subgroup of any such defect is
  free abelian.  The finite central witness of the torsion theorem is
  infinite cyclic here.
- **Properly infinite corner**
  (`properly-infinite-corner-forces-non-mf-from-rank-two`).  Dead: no
  matrix ring over `J_Z` has a nonzero properly infinite idempotent.  The
  symbol image of such an idempotent is an idempotent `p` in a matrix ring
  over the field `Q(z)` with `y_0 x_0 = p = y_1 x_1`, `y_0 x_1 = 0` inside
  `pMp`; then `x_0` is bijective on `pV`, so `y_0` is its inverse there,
  `x_1 = 0` on `pV`, and `p = y_1 x_1 = 0`.  So the idempotent has finite
  rank on `V^n`, and rank additivity forbids `p ~ p (+) p`.
- **Rank descent from the binary case.**  Dead in the other direction:
  `EL_n(J_Z)` surjects onto the non-MF `EL_n(J_(F_p))`, but MF is not
  inherited by quotients, and MF passes to subgroups, not the other way.
- **Intermediate radicals.**  Excluded: the radical is `1` or
  `SL_fin(Z)`, so no congruence-type or partial collapse can be the
  answer (`integral-jacobson-mf-radical-is-all-or-nothing`).
- **What a proof would need.**  Either an obstruction that sees the
  infinite cyclic central element `z = diag(1,1,1,1 + f_12)` in the
  defect, whose MF images are trivial or of infinite order, or a
  finite-order element of the defect of a different shape, or an
  argument that does not go through the defect at all; or, for the
  other side, one operator-norm approximate representation of
  `EL_4(J_Z)` that is exact enough on the residually finite symbol part
  and keeps `z` at infinite order.
