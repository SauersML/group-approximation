---
rg: 2
id: k-uniform-hypergraph-vertex-cover-hardness-without-ugc
kind: claim
title: Tight k-uniform hypergraph vertex cover hardness holds without the Unique Games Conjecture (Karthik--Minzer)
artifacts:
  - research/artifacts/karthik-minzer-multilayered-pcp-source-2026-09-11.md
distinct_from:
  unique-games-conjecture: that is Khot's conjecture itself; this is an unconditional NP-hardness theorem for one of its classical consequences (Khot--Regev 2008) and implies nothing about the conjecture in either direction.
---

**ESTABLISHED, BY CITATION (unrefereed preprint).** For every `k >= 4` and
every `eps > 0`, it is NP-hard to approximate the minimum weight of a vertex
cover of a `k`-uniform weighted hypergraph within factor `k - eps`. For `k = 3`
the same holds within factor `1 + sqrt(2) - eps`.

Source: Karthik C. S. and Dor Minzer, *Improved Multilayered PCPs and
Hypergraph Vertex Cover*, arXiv:2609.06775v1 (6 September 2026), Theorem 1.6.
The factor `k - eps` is tight, since a simple polynomial-time algorithm gives
ratio `k`. It was previously known only assuming the Unique Games Conjecture
(Khot--Regev, JCSS 2008); the best unconditional factor was `k - 1 - eps`
(Dinur--Guruswami--Khot--Regev, SICOMP 2005). The proof goes through a
multilayered projection label cover with 2-to-2 constraints and completeness
`1 - eps` (Theorem 1.4 there). The authors state that the results were first
obtained with ChatGPT 5.6 Pro and then rewritten by them.

**Scope.** This removes the UGC hypothesis from one of its consequences. It
is not a route into `unique-games-conjecture`, and it neither proves nor
refutes it. It is recorded because its 2-to-2 multilayered construction works
in the near-1 completeness regime that the rich 2-to-1 attacks need; see the
source record for the theorem statements and the caveat on Theorem 1.4.
