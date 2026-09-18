---
rg: 2
id: amenable-f-infinity-groups-of-finite-cd-are-virtually-soluble
kind: claim
title: Every amenable group of type F_infinity and finite cohomological dimension is virtually soluble
distinct_from:
  amenable-groups-of-finite-cd-are-virtually-solvable: that is Kropholler's question with no finiteness hypothesis; this adds type F_infinity, so it is the special case that the F_infinity problem actually needs.
  every-f-infinity-amenable-group-is-elementary-amenable: that allows infinite cohomological dimension and contains the Thompson F problem; this assumes finite cohomological dimension and does not mention F.
  amenable-finite-cd-domain-groups-are-virtually-solvable: that assumes Z[G] is a domain and no finiteness of type; this assumes type F_infinity and nothing about zero divisors.
  f-infinity-groups-of-finite-cd-are-of-type-f: that asks whether F_infinity plus finite cd gives a finite classifying space, with no amenability; this asks for virtual solubility under amenability.
---

**OPEN.** Let `G` be an amenable group of type `F_∞` with `cd_Z G < ∞`. Then `G`
has a soluble subgroup of finite index.

This is the **finite-dimensional half** of the decomposition
`f-infinity-amenable-ea-via-finite-vcd-and-finite-cd-case`. The target
`every-f-infinity-amenable-group-is-elementary-amenable` holds exactly when this
claim and `amenable-f-infinity-groups-have-finite-vcd` both hold.

It is a special case of Kropholler's question
`amenable-groups-of-finite-cd-are-virtually-solvable`
(route `amenable-f-infinity-finite-cd-soluble-via-kropholler-question`). Nothing
here goes the other way: a counterexample to Kropholler's question that is not of
type `F_∞` does not refute this claim.

## Attempts

- **Low dimensions.**
  - `cd G ≤ 1`: `G` is free (Stallings–Swan) and amenable, so `G` is trivial or `Z`.
  - `cd G = 2`, conditional on `Z[G]` being a domain: Degrijse, arXiv:1609.07635v1,
    Theorem B, verbatim: "Every amenable group G of cohomological dimension 2 such
    that Z[G] is a domain is solvable and hence isomorphic to a solvable
    Baumslag-Solitar group BS(1, m) for some non-zero m ∈ Z or to a non-cyclic
    subgroup of the additive rationals."
  - So the first open case is `cd G = 2` without the domain hypothesis, or
    `cd G = 3`.
  - Degrijse's proof of Theorem B (p. 11) runs: type `FP`, Euler characteristic 0,
    `b_1 > 0`, then an HNN splitting over a finitely generated base. Here type `FP`
    is free: `FP_∞` plus finite cd gives `FP` (Brown, *Cohomology of Groups*,
    VIII.6). The domain hypothesis is used to get `FP` in Degrijse's Theorem A, and
    again later in that proof. This lane did not check whether the later uses can be
    removed under `F_∞`.
- **Infinite vcd plays no role.** No known amenable group that is not elementary
  amenable has finite cohomological dimension over any field (Degrijse, quoted in
  `amenable-f-infinity-groups-have-finite-vcd`). So this half has no candidate
  counterexample from branch groups or topological full groups. A counterexample
  here would also answer Kropholler's question negatively.
