---
rg: 2
id: bnsr-invariants-stabilize-at-cohomological-dimension
kind: claim
title: "A group of type F_infinity and finite cohomological dimension d has Sigma^m(G) = Sigma^max(d,2)(G) for all m >= max(d,2)"
distinct_from:
  every-f-infinity-group-has-open-sigma-infinity: that claim asserts openness of Sigma^infinity for every group of type F_infinity; this theorem proves it only for groups of finite cohomological dimension, by showing the invariants stabilize.
  non-open-sigma-infinity-needs-unbounded-sigma-depth: that lemma is pure point-set topology about the depth function; this theorem is homological algebra bounding where the invariants of a finite-dimensional group can still change.
---

Let `G` be a group of type `F_∞` with `cd G = d < ∞`. Then

- `Σ^m(G;Z) = Σ^d(G;Z)` for all `m ≥ d`, and
- `Σ^m(G) = Σ^{max(d,2)}(G)` for all `m ≥ max(d,2)`.

In particular `Σ^∞(G) = Σ^{max(d,2)}(G)` and `Σ^∞(G;Z) = Σ^d(G;Z)` are open in
the character sphere.

This covers every group with a finite classifying space (type F), where
Ershov–Zaremsky record the statement `Σ^n(G) = Σ^∞(G)` for a finite classifying
space of dimension `n` (arXiv:2505.18826, §2.1). It also covers any group of
type `F_∞` with finite cohomological dimension that is not of type F, if one
exists (Problem 1.21, `zaremsky-1-21-g-times-z-type-f-implies-g-type-f`).

**Consequence for Problem 1.13.** A group of type `F_∞` whose `Σ^∞(G)` is not
open has infinite cohomological dimension.

**Model tests.** `F_2^r` has `cd = r` and `Σ^r(F_2^r) = ∅ = Σ^∞`, so the bound
is attained. The pure braid group `P_n` has `cd = n−1`; the theorem gives
stabilization from index `max(n−1,2)`, consistent with Zaremsky's sharper
`Σ^∞(P_n) = Σ^{n−2}(P_n)` (arXiv:1507.08597). Thompson's group `F` has infinite
cohomological dimension, so the theorem says nothing about it; its invariants
stabilize at `m = 2` for other reasons.

Proof: `bnsr-invariants-stabilize-at-cohomological-dimension-proof`.
