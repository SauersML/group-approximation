---
rg: 2
id: rank-density-and-strict-comparison-give-purity
kind: claim
title: Uniform density of rank functions plus strict comparison makes a simple exact algebra pure
distinct_from:
  thiel-stable-rank-one-ranks-close-purity-with-comparison: that derives purity from exact rank realization under stable rank one; this derives it from mere uniform approximation of continuous affine functions by ranks, with no stable rank hypothesis.
  stw99-problem-xxvii-comparison-vs-divisibility: that asks whether strict comparison alone gives purity; this proves it once rank functions are uniformly dense, so a counterexample there must fail rank density.
  strict-comparison-rank-surjectivity-forces-sr1: that is Lin's theorem that strict comparison plus a surjective rank map forces stable rank one; this needs only density of ranks and concludes purity.
artifacts:
  - research/artifacts/toms-winter-rank-density-firewall-2026-09-11.md
---

Let `A` be a unital simple separable exact stably finite non-elementary
C-star algebra with strict comparison of positive elements with respect to
`T(A)`.  Suppose rank functions are uniformly dense (RD): for every
continuous strictly positive affine `f` on `T(A)` and `eta > 0` there is
`y in M_infty(A)_+` with `|d_tau(y) - f(tau)| < eta` for all `tau`.  Then
`Cu(A)` is almost divisible: for `x' << x` in `Cu(A)` and `k in N` there is
`y` with `k y <= x` and `x' <= (k+1) y`.  Hence `A` is pure.

Contrapositive, which is how this node is used: a strict-comparison algebra
that is not pure has a continuous strictly positive affine function on its
trace simplex that no rank function approximates within some fixed `eta`
everywhere.  Such an algebra fails approximate rank realization, not just
exact rank realization.
