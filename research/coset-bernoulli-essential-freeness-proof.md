---
rg: 2
id: coset-bernoulli-essential-freeness-proof
kind: route
title: Building convexity plus orbit independence prove essential freeness
target: coset-bernoulli-action-is-essentially-free
requires: []
---

Complete direct proof; full text in
`research/artifacts/coset-wreath-cartan-entropy-2026-08-22.md`
(Theorem 1).

Skeleton.  (i) `Stab_{SL_3(Q_3)}(v_0) = SL_3(Z_3)` by the determinant
computation on lattice classes, so `Stab_Gamma(v_0) = SL_3(Z)` and
strong approximation identifies `Gamma/Lambda` with the type-0 vertices
of the building.  (ii) If `g` fixes all type-0 vertices outside a ball,
then for every apartment `A` and every `x in A` three far type-0
lattice vertices of `A` in directions 120 degrees apart span a Euclidean
triangle containing `x`; apartments are convex, fixed sets of isometries
are convex, so `x` is fixed; hence `Fix(g)` is the whole building and
`g` lies in the kernel, which is `mu_3(Q_3) = 1` since `-3` has odd
3-adic valuation.  (iii) Given infinitely many moved cosets, pick
infinitely many disjoint nontrivial `<g>`-orbits; constancy on each is
an independent event of probability at most `1/2`, so the fixed-point
set of `g` in `{-1,1}^I` is null; countably many `g` finish.

External inputs, statement level: Bruhat–Tits building of `SL_n(Q_p)`
with convex apartments and kernel-equals-center; strong approximation
for `SL_3` at `S = {infinity, 3}`.  Both are textbook-grade.
