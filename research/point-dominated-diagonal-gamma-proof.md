---
rg: 2
id: point-dominated-diagonal-gamma-proof
kind: route
title: Colour constant evaluation blocks by vector discrepancy and discard the coordinate mass
target: point-dominated-diagonal-ah-has-uniform-gamma
requires: []
artifacts:
  - research/artifacts/stw99-xx-point-dominated-diagonal-gamma-2026-08-30.md
---

Fix `k>=2`, a stage `n`, and a finite set `F` in the unit ball of its
building block; enlarge `F` to contain the unit.  For a later composite,
separate the `L` eigenvalue maps
into `C` coordinate maps and `P=L-C` point evaluations at points
`x_1,...,x_P` (repetitions are allowed).  For `a in F`, put

`z_i(a)=tr_(r_n)(a(x_i))`.

Independently colour each point-evaluation block uniformly by one of
`1,...,k`.  For a colour `ell`, set

`D_(ell,a)=sum_(i=1)^P (1_(colour(i)=ell)-1/k) z_i(a)`.

The variables have mean zero and

`E |D_(ell,a)|^2 <= sum_i |z_i(a)|^2 <= P`.

Therefore some colouring satisfies simultaneously, for every `a in F`
and every `ell`,

`|D_(ell,a)| <= sqrt(k |F| P)`.

(Indeed the expectation of the sum of these squared discrepancies is at
most `k|F|P`.)  Colour the remaining `C` coordinate blocks arbitrarily.
Let `e_ell` be the block-scalar projection selecting colour `ell`, and
conjugate it by the unitary in the diagonal form to obtain a continuous
projection `p_ell` in the later building block.  The projections are
orthogonal, sum to one, and commute exactly with `phi_(n,m)(A_n)`.

For `a in F`, at every base point `y`, normalized matrix trace gives

`tr(p_ell phi_(n,m)(a))(y)-tr(phi_(n,m)(a))(y)/k
 = L^(-1) D_(ell,a) + E_coord(y)`,

where `|E_coord(y)|<=C/L`.  Hence, uniformly in `y`,

`|tr(p_ell phi_(n,m)(a))-tr(phi_(n,m)(a))/k|
 <= sqrt(k|F|P)/L + C/L`.                              `(PDG1)`

Every trace on the later homogeneous block is obtained by integrating
the normalized fibre trace, so `(PDG1)` holds for every restriction of a
limit trace.

Choose increasing stages `n_j` with dense union and finite sets `F_j`
whose images together are dense in the unit ball of the limit.  The
hypotheses allow later stages `m_j`
for which both terms on the right of `(PDG1)` tend to zero: `C/L->0`,
while `sqrt(P)/L<=1/sqrt(L)->0`.  Embed the resulting projections in the
limit.  They commute exactly with the image of `A_(n_j)`, hence form
norm-central sequences, and `(PDG1)` gives the required uniform tracial
splitting on a dense subset and therefore on all of `A`.  Their classes
in the uniform tracial ultrapower prove uniform property Gamma.

For `k=2`, put `h_j=2p_j^(1)-1`.  Centrality is unchanged and the trace
estimate becomes
`sup_tau |tau(a h_j)|->0`, giving the announced trace-zero contractions.
