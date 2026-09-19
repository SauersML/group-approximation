---
rg: 2
id: artin-sigma1-conjecture-fails-for-an-even-k4-artin-group
kind: claim
title: "The Sigma^1-conjecture for Artin groups is false: an even 2-dimensional Artin group on four vertices has a character in Sigma^1 with disconnected living subgraph"
distinct_from:
  artin-sigma1-is-connected-dominant-living-subgraph: that is the conjecture; this is an explicit counterexample to its necessity half (Liv disconnected implies not in Sigma^1). The conjecture node should carry refuted_by this claim.
  artin-k4-mixed-dead-character-lies-in-sigma1: that is the membership statement for one character; this adds the living-subgraph computation and records the consequence for the conjecture
---

Let `K` be the complete graph on `u1, u2, v1, v2` with labels
`l(u1u2) = l(v1v2) = 2`, `l(u1v1) = l(u2v1) = l(u2v2) = 4`, `l(u1v2) = 6`, and let
`χ = (1, 1, -1, -1)`.

**Claim.**
- `[χ] ∈ Σ^1(A_K)`.
- `Liv^χ = {u1–u2} ⊔ {v1–v2}` is disconnected.

So `Σ^1(A_K) != {[χ] : Liv^χ connected and dominant}`.

`A_K` is even and 2-dimensional (no spherical triangle), and so satisfies the
`K(π,1)` conjecture. It lies outside all proved families:
- the 4-cycle of labels `> 2` has even length (Kochloukova);
- `2` and `3` share no prime (the prime-`p` family);
- it is not balanced, and not coherent.
