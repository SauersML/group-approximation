---
rg: 2
id: marked-limits-of-special-groups-domain-proof
kind: route
title: Combine the local transfer of domains with Fisher--Sanchez-Peralta's division rings for special groups
target: marked-limits-of-special-groups-have-domain-group-rings
requires:
  - group-ring-domains-pass-to-local-embeddings
  - fisher-sanchez-peralta-special-and-3-manifold-domains
---

**Proof.** Let `k` be a field. Each `H_n` is torsion-free and virtually the
fundamental group of a compact special cube complex. So item 1 of
`fisher-sanchez-peralta-special-and-3-manifold-domains` embeds `k[H_n]` in a
division ring, and `k[H_n]` is a domain. The corollary of
`group-ring-domains-pass-to-local-embeddings` then makes `k[G]` a domain. The
general form is the claim of that node with every `H` taken in the special
class.

**Finite presentation remark.** If `G` is finitely presented by relators of
length at most `L`, then for large `n` every relator holds in `(H_n, S_n)`,
since balls of radius `L` agree. So `S -> S_n` extends to a homomorphism
`phi_n: G -> H_n` that is injective on balls of growing radius. The approximants
are therefore images of `G`, and the condition says `G` is fully residually
(torsion-free virtually compact special) along a sequence of quotients.
