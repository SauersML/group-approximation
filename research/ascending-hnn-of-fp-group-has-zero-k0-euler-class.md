---
rg: 2
id: ascending-hnn-of-fp-group-has-zero-k0-euler-class
kind: claim
title: "An ascending HNN extension of a group of type FP has zero K_0 Euler class, so it is of type F iff finitely presented"
distinct_from:
  g-times-z-type-f-iff-g-f-infinity-with-finite-cd: that is the case of the identity endomorphism, G x Z; this covers every injective endomorphism, including all semidirect products N x| Z with N of type FP
  stallings-group-has-a-type-f-mapping-torus: that exhibits one explicit type F mapping torus of a base that is not FP_3; this is a general Euler-class vanishing theorem for bases of type FP
  fp-type-fp-group-is-type-f-iff-wall-class-vanishes: that is the criterion F iff sigma(G) = 0 for finitely presented FP groups; this computes that the class vanishes for every ascending HNN extension of an FP base
artifacts:
  - research/artifacts/zaremsky-1-21-fibering-and-retracts-2026-09-16.md
---

Let `B` be a group of type FP, `φ: B → B` an injective endomorphism, and

```text
G = B*_φ = ⟨B, t | t b t⁻¹ = φ(b), b ∈ B⟩.
```

Then:

- `G` is of type FP with `cd G ≤ cd B + 1`;
- the K_0 Euler class `χ_G = Σ_i (−1)^i [P_i] ∈ K_0(ZG)` of any finite
  projective resolution is `0`, so the Wall class `σ(G) ∈ K̃_0(ZG)` and the
  Euler characteristic `e(G)` both vanish;
- `G` is of type FL;
- `G` is of type F iff `G` is finitely presented, for instance when `B` is.

**Corollary (fibred groups).** A finitely presented group `G` that admits an
epimorphism `G → Z` whose kernel is of type FP is of type F. Indeed
`G ≅ N ⋊ Z` is the HNN extension of `N` along an automorphism.

For Problem 1.21 (`f-infinity-groups-of-finite-cd-are-of-type-f`), a
counterexample does not fibre over `Z` with an FP fibre, and it is not an
ascending HNN extension over any FP base.

Model tests:

- `φ = id` recovers `G × Z`.
- `BS(1,n)` has `e = 0`.
- For an acyclic flag complex `L` that is not simply connected, the
  Bestvina–Brady group `BB_L` is FP but not finitely presented, while
  `A_L = BB_L ⋊ Z` is finitely presented and of type F. So the base need not
  be finitely presented.

This is the algebraic form of the mapping-torus identity in Wall's
finiteness theory. Proof: `ascending-hnn-zero-k0-euler-class-proof`.
