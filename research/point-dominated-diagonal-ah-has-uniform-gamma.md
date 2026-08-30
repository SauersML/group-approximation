---
rg: 2
id: point-dominated-diagonal-ah-has-uniform-gamma
kind: claim
title: Point-dominated diagonal AH systems have uniform property Gamma
distinct_from:
  stw99-problem-xx-villadsen-algebras-uniform-gamma: that asks about the positive-coordinate-weight Villadsen regime; this proves the complementary diagonal class where the nonconstant coordinate weight vanishes.
  stw99-problem-xix-uniform-gamma-stably-finite-nuclear: that asks for uniform Gamma without a model; this uses a quantitative diagonal eigenmap hypothesis and constructs the central projections at finite stages.
artifacts:
  - research/artifacts/stw99-xx-point-dominated-diagonal-gamma-2026-08-30.md
---

Let

`A=lim_n (C(X_n) tensor M_(r_n), phi_n)`

be a unital simple diagonal AH algebra.  For `m>n`, write the composite
map, up to continuous unitary conjugacy, as

`phi_(n,m)(a)(y)=diag(a(lambda_1(y)),...,a(lambda_L(y)))`,

where `L=L_(n,m)=r_m/r_n`, and every eigenvalue map is either a coordinate
map or a constant point evaluation.  Let `C_(n,m)` be the number of
nonconstant coordinate maps, counted with multiplicity.  Assume that for
every `n`,

`liminf_(m->infinity) (L_(n,m)^(-1)+C_(n,m)/L_(n,m))=0`.

Equivalently, from each fixed stage one can choose a cofinal subsequence
on which the total multiplicity tends to infinity and the proportion of
nonconstant coordinate maps tends to zero.

Then `A` has uniform property Gamma.

More concretely, for every `k>=2` there are pairwise orthogonal
projections `p_j^(1),...,p_j^(k)` in later building blocks, summing to one,
such that they asymptotically commute in norm with `A` and

`sup_(tau in T(A)) |tau(a p_j^(ell))-tau(a)/k| -> 0`

for every `a in A` and every `ell`.  For `k=2`, the selfadjoint unitaries
`h_j=2p_j^(1)-1` are norm-central contractions satisfying

`sup_tau |tau(a h_j)| -> 0`

for every `a`; thus the construction directly supplies uniform
trace-zero central contractions.
