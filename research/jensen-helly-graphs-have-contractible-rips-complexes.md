---
rg: 2
id: jensen-helly-graphs-have-contractible-rips-complexes
kind: claim
title: Bounded-degree graphs with a k-dimensional Jensen–Helly realization have contractible Rips complexes at t ≥ k(k+1) − 1
distinct_from:
  zaremsky-rips-contractibility-criterion: that is the general Morse criterion about enclosing balls and their centres; this is a checkable geometric property (barycentres, Helly number, rounding) that implies the criterion's hypotheses
---

Let `G` be a connected graph with uniformly bounded degrees, vertex set `V`
and path metric `d`. Say `G` has the **Jensen–Helly property of dimension
`k`** if there is a metric space `(|G|, d)` containing `(V, d)` isometrically
with three properties.

- **(J) Jensen barycentres.** For every finitely supported probability measure
  `μ` on `V` there is `b(μ) ∈ |G|` with `d(x, b(μ)) ≤ ∫ d(x,y) dμ(y)` for
  every `x ∈ V`.
- **(H) Helly number `k+1`.** For every finite family of balls
  `B(z,ρ) = {c ∈ |G| : d(z,c) ≤ ρ}` with `z ∈ V`: if every `k+1` members have a
  common point, all members have a common point.
- **(R) Rounding.** Every `c ∈ |G|` lies within `k/2` of some vertex.

**Theorem.** If `G` has the Jensen–Helly property of dimension `k ≥ 1`, then
`VR_t(V)` is contractible for every integer `t ≥ k(k+1) − 1`.

Instances: l^1 products of `k` bounded-degree trees, with `|G|` the product of
the realizations. There (J) is Lemma J coordinatewise, (H) is Lemma H, and (R)
is Lemma R of `research/artifacts/zp-raag-rips-products-of-trees-2026-09-13.md`.
For (H) on all of `|G|`, first move the finitely many witness points into the
product `P` of the finite subtrees spanned by the centres and witnesses. The
coordinatewise nearest-point projection onto `P` does not increase `d_1` to
points of `P`, so Lemma H applies inside `P`.
Model test: `Z^n` with `d_1` and `|G| = R^n` satisfies (J) through the mean and
(H) through Euclidean Helly on convex sets. The resulting bound
`t ≥ n^2 + n − 1` matches arXiv:2410.11993, Corollary 3.2.

UNREVIEWED. Proof: route
`jensen-helly-graphs-have-contractible-rips-complexes-proof`.
