---
rg: 2
id: group-ring-domains-pass-to-local-embeddings
kind: claim
title: If every finite piece of a group embeds multiplicatively into a group whose group ring is a domain, then the group ring is a domain
distinct_from:
  local-approximation-properties-are-marked-closed: that proves closure of approximation properties such as soficity under marked limits; this is the ring-theoretic statement that the group ring over a fixed field is a domain, which is not an approximation property.
  zero-divisor-support-subgroup-host-constraints: that lists which properties the support subgroup of a zero divisor must violate; this shows the domain property itself is a local property of the group.
  kaplansky-zero-divisor-conjecture: that is the conjecture for every torsion-free group; this is an elementary closure property that decides no instance by itself.
---

**ESTABLISHED** (elementary; no novelty claimed). Let `k` be a field and `G` a
group. Suppose that for every finite subset `F ⊆ G` containing `1` there are a
group `H` such that `k[H]` is a domain and a map `psi: F·F -> H` with

- `psi` injective on `F·F`, and
- `psi(ab) = psi(a) psi(b)` for all `a, b in F`.

Then `k[G]` is a domain.

**Corollary (marked limits).** If a finitely generated marked group `(G, S)` is
the limit of marked groups `(H_n, S_n)` in the space of marked groups, and
`k[H_n]` is a domain for infinitely many `n`, then `k[G]` is a domain. For a
fixed radius `R`, the balls of radius `2R` of `G` and of `H_n` agree for large
`n`, and the resulting identification is a map `psi` as above with `F` the ball
of radius `R`.

DERIVATION
[[group-ring-domains-local-embedding-proof]]
