---
rg: 2
id: finite-additive-order-one-sided-defects-are-mf-invisible
kind: claim
root: true
title: Every one-sided inverse defect of finite additive order is MF-invisible in elementary rank at least four
distinct_from:
  locally-finite-defect-subgroup-dies-in-every-corona: that asks for arbitrary locally finite normal subgroups; this settles all finite-additive-order ring defects through a special finitary elementary subgroup with a uniform rank bound.
  binary-jacobson-steinberg-head-root-is-mf-invisible: that is the binary Jacobson group in rank five; this covers arbitrary coefficient rings and every finite additive order in rank four.
artifacts:
  - research/artifacts/rank-weighted-locally-finite-compression-2026-09-08.md
  - research/artifacts/composite-jacobson-uniform-rank-and-normality-2026-09-08.md
  - research/artifacts/finite-order-one-sided-defect-mf-collapse-2026-09-08.md
  - research/artifacts/jacobson-unit-group-and-rank-four-recheck-2026-09-08.md
  - research/artifacts/finite-rank-compression-defect-dichotomy-2026-09-09.md
  - non_mf_groups_exist.tex
---

Let R be a countable unital ring, s,t in R satisfy ts=1, and let
Q=1-st have finite additive order. For every n>=4 and i!=j,

    e_ij(Q) belongs to Rad_MF(E_n(R)).

If Q!=0, E_n(R) is not MF. No assumption RQR=R is needed. In
particular, for rings of positive characteristic, MF of E_4(R)
implies direct finiteness of R.

The proof uses property (T) on an elementary subgroup over a
finitely generated universal ring. It is not a property-(T)-free
proof and carries no new Lean verification claim.

**Independently corroborated, at a worse rank (2026-09-08).**  A forwarded
dossier derived this criterion from scratch under the same hypotheses -- `R`
countable unital, `ts = 1`, `Q = 1 - st` of finite additive order, no fullness
assumption -- and reached `E_n(R, RQR) <= Rad_MF(EL_n(R))` for `n >= 6`, by
building a dilation `v = [[s,Q],[0,t]]` with an explicit elementary
factorisation, a unit `r = (1+sQ)(1-Qt)(1+sQ)` making the compressor
`u = UP` normalise `EL_3` in six coordinates, and then applying
`normal-kazhdan-defect-non-mf` to a finite central `<x_56(Q)>` inside the
subgroup it generates.  Its analytic input is the same, Ershov--Jaikin-Zapirain
Theorem 1.1 for property (T) of the elementary group over a finitely generated
subring.  So the statement above has a second derivation by a different
compressor; the rank there is `6` and the rank here is `4`, so nothing is
gained by adopting it and a reader comparing the two should take `n >= 4`.

The dossier also drew out the instance `R = J = F_2<s,t | ts = 1>` at `n >= 6`,
which is `binary-jacobson-steinberg-head-root-is-mf-invisible`, proved here at
rank five.  Its one genuinely additive observation is the criterion-level
dichotomy recorded on
`kazhdan-criterion-is-inert-on-finitary-permutation-extensions` and
`finitary-linear-extension-kazhdan-defect-kills-kernel`, with the ingestion
record in
`research/artifacts/finitary-linear-vs-permutation-kazhdan-criterion-2026-09-08.md`.

**A Kazhdan-free proof exists in finite dimensions, and stops there
(2026-09-08).**  `uniform-root-kernel-invariance-kills-one-sided-defect`
kills the same defect roots in every exact finite-dimensional unitary
representation of `E_n(R)`, `n >= 3`, using only a spectral gap at the
`m`-th roots of unity and the fact that a left-invertible endomorphism of a
finite abelian group is invertible -- no property (T), no
Ershov--Jaikin-Zapirain, no simplicity or fullness.  What it needs is
uniformity over coefficients at a single coordinate, and
`root-kernel-invariance-is-not-pointwise-obtainable` proves that pointwise
corona data does not supply it, with every fixed test eventually exact and
the invariance failing at distance `2` at every coordinate.  So the
statement above still consumes property (T), and this is a recorded dead
route to removing it rather than a second proof.

**A THIRD derivation arrived, again at a worse-or-equal rank
(2026-09-08).**  The same dossier lane returned with a rank-four proof,
presented as improving its own rank-six one.  It lands exactly here: same
hypotheses, same conclusion `E_n(R,ReR) <= Rad_MF(EL_n(R))` for `n >= 4`,
same positive-characteristic corollary.  Its compressor is genuinely
different and is the reason it reaches four in one step -- the ring's own
matrix units `f_(ij) = s^i e t^j` let ONE auxiliary coordinate hold every
finite witness, leaving three for the Kazhdan subgroup, with
`u = U diag(1,1,1,r)`, `U` carrying `s,s,s,t^3` and last column
`e, et, et^2`, inverted by `e + set + s^2et^2 = 1 - s^3t^3`, central
witness `z = I + set^2 E_44`, and extraction
`[z, x_41(s^2e)] = x_41(se)`, `[x_24(t), x_41(se)] = x_21(e)`.  Those
identities were rechecked here in the normal form `s^i t^j`.  Nothing in
the statement is gained, but the derivation is wired as its own route,
`torsion-defect-one-auxiliary-coordinate-proof` (2026-09-09): it is the
proof printed in the manuscript as `prop:torsion-defect-ring`, and it
consumes only `normal-kazhdan-defect-non-mf` inside a subgroup plus
Ershov--Jaikin-Zapirain property (T), whereas the first route runs
through the rank-weighted transport lineage that the manuscript excludes
on provenance grounds.  The compressor is also recorded in
`research/artifacts/jacobson-unit-group-and-rank-four-recheck-2026-09-08.md`.

**Exactness, and the characteristic-zero boundary (2026-09-09).**  For
the universal rings `A_m = Z<s,t | ts = 1, m(1-st) = 0>` the inclusion
is an equality, `Rad_MF(E_n(A_m)) = E_n(A_m, A_m e A_m) = SL_fin(Z/m)`
for `n >= 4` (`universal-torsion-defect-rings-have-exact-mf-radical`);
for `m > 2` the symbol kernel exceeds the radical by a central sign that
survives in a finite quotient.  Over `J_Z = Z<s,t | ts = 1>` itself the
same configuration gives an infinite cyclic central `z`, and no
compression defect of any subgroup of `GL_n(J_Z)`, at any rank, contains
a nontrivial normal Kazhdan subgroup
(`integral-jacobson-defect-has-no-normal-kazhdan-subgroup`): the finite
additive order hypothesis is exactly what makes the witness finite and
hence Kazhdan.  At rank two the criterion is inert over every `A_m` and
every finite-field Jacobson algebra, because those rank-two groups have
no infinite Kazhdan subgroup at all
(`rank-two-jacobson-groups-have-no-infinite-kazhdan-subgroup`); rank
three is open.

The same note's unit-group half was **already weaker than this archive**:
its "full torsion defect implies `R^x` non-MF" is
`properly-infinite-unit-group-is-not-mf` without any torsion or
characteristic hypothesis, and its "properly infinite corner in positive
characteristic" is `properly-infinite-corner-forces-non-mf-from-rank-two`
without the characteristic hypothesis and at rank two.  Its one new
result is `jacobson-unit-group-is-locally-finite-and-mf`, which shows the
rank-one statement is false and so bounds this line from below.
