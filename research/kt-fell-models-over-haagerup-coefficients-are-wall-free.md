---
rg: 2
id: kt-fell-models-over-haagerup-coefficients-are-wall-free
kind: claim
title: Canonical Fell models of the Kun--Thom group with a Haagerup coefficient carry no relative wall
distinct_from:
  haagerup-targets-carry-no-relative-wall: that excludes targets in which the Kazhdan image itself is Haagerup, which no canonical model is; this excludes the canonical models lambda tensor pi whose coefficient image is Haagerup, where the ambient algebra contains the property (T) algebra L(Gamma).
  fell-models-inherit-walls-from-coefficients: that is the general wall-transfer identity for subgroups with infinite conjugacy classes; this is its application to the binary Kun--Thom pair with Haagerup coefficients.
---

**ESTABLISHED.** Let `Gamma <= G` be the binary Kun--Thom Theorem E pair, let
`(M_0,tau_0)` be a finite von Neumann algebra, and let `pi : G -> U(M_0)` be a
homomorphism such that `pi(Gamma)''` has the Haagerup property (for example
`M_0` amenable). Then the canonical model
`sigma = lambda tensor pi : G -> U(L(G) tensor-bar M_0)` normalizes
`sigma(Gamma)' cap (L(G) tensor-bar M_0)`, and no family in that algebra has
commutation stabilizer `Gamma`.

So the canonical models produced from Haagerup coefficients by tensoring with
the regular representation — the natural outputs of
`ce-stabilizer-criterion-needs-no-trace` — cannot witness
`kt-subgroup-is-a-ce-commutation-stabilizer` and carry no wall toward
`kt-centralizer-normalization-hs`. Any wall model must be genuinely non-Fell or
use a non-Haagerup coefficient.

DERIVATION
kt-fell-haagerup-wall-free-proof
