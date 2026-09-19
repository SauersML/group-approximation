---
rg: 2
id: corona-commutant-no-growth-via-uniform-stability
kind: route
title: Lift the corona representation by uniform stability, then collapse in finite dimensions
target: corona-commutant-no-growth
requires: []
artifacts:
  - research/artifacts/glmr-2301-00476-verified.md
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

Use uniform (Ulam) stability of `Gbar = Z^3 semidirect SL_3(Z)` in the
operator norm to replace the coordinate maps of a corona representation by
genuine finite-dimensional unitary representations, then apply
`commutant-no-growth` coordinatewise: in a genuine representation the
commutant of the compressed Kazhdan image already equals that of the Kazhdan
image, by comparing dimensions.

Dead: `corona-defect-is-not-uniform`.  Uniform stability hypothesizes that the
coordinate defect is small *uniformly over all pairs of group elements*, while
a corona representation of an infinite group supplies only pointwise vanishing
defect — multiplicativity on balls of slowly growing radius.  No choice of
lifts repairs this.  The route therefore fails before the group class matters,
and in particular it does not depend on whether the Glebsky--Lubotzky--Monod--
Rangarajan theorems cover the affine group, which the repository has not
verified at source level.

The surviving form of this idea is the same reduction with *matricial*
stability (Dadarlat, Adv. Math. 2021) in place of uniform stability: that
notion is stated for lifting homomorphisms into the matrix corona, which is
exactly the hypothesis available here.  Whether the affine Kazhdan group is
matricially stable in the operator norm is open, and is the live version of
this attack.
