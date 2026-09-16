---
rg: 2
id: virtually-finite-cd-f-infinity-groups-have-stable-bnsr
kind: claim
title: "If G is of type F_infinity and has a finite-index subgroup of cohomological dimension d, then Sigma^m(G) = Sigma^max(d,2)(G) for all m >= max(d,2)"
distinct_from:
  bnsr-invariants-stabilize-at-cohomological-dimension: that claim needs cd G itself finite, so G is torsion-free; this one needs only a finite-index subgroup of finite cd, so it covers groups with torsion such as every group of type VF
  cocompact-contractible-d-complex-bnsr-stabilize-at-d: that claim needs a proper cocompact action of G on a contractible finite-dimensional complex; this one needs no cocompact model for proper actions, only a finite-index subgroup of finite cohomological dimension
---

Let `G` be a group of type `F_∞` with a subgroup `H` of finite index and
`cd H = d < ∞`. Then

`Σ^m(G) = Σ^{max(d,2)}(G)` for every `m ≥ max(d,2)`.

In particular `Σ^{max(d,2)}(G) = Σ^{max(d,2)+1}(G)`, so no group of type
`F_∞` that is virtually of finite cohomological dimension answers Zaremsky
Problem 1.18 affirmatively.

- **Type VF.** The hypothesis holds when some finite-index subgroup has a
  finite classifying space.
- **Torsion.** The group `G` may have torsion. No proper cocompact action on a
  finite-dimensional contractible complex is assumed, so this claim is not a
  case of `cocompact-contractible-d-complex-bnsr-stabilize-at-d`.

Proof: `virtually-finite-cd-stable-bnsr-via-finite-index-detection`.
