---
rg: 2
id: artin-k4-odd-family-dead-characters-lie-in-sigma1
kind: claim
title: "For every odd q, the dead character (1,1,-1,-1) of the four-vertex Artin group with cross labels 4,4,4,2q lies in Sigma^1: infinitely many counterexamples to the Sigma^1-conjecture"
distinct_from:
  artin-k4-mixed-dead-character-is-outside-sigma1: that predicts non-membership for q = 3; this proves membership for every odd q, so q = 3 refutes it
  artin-k4-dead-cut-admits-no-nonzero-dead-edge-ring: that shows the ring method is empty for q = 3; this proves membership, and shows the dead-edge sums generate the unit left ideal of Z[ker chi] already
  artin-sigma1-is-connected-dominant-living-subgraph: that is the conjecture; this is an infinite family of counterexamples to its necessity half
artifacts:
  - experiments/artin-k4-odd-family-2026-09-17/odd_family_identity.py
  - experiments/artin-k4-odd-family-2026-09-17/odd_family_identity.log
---

For `q >= 2` let `K_q` be the complete graph on `u1, u2, v1, v2` with labels
`l(u1u2) = l(v1v2) = 2`, `l(u1v1) = l(u2v1) = l(u2v2) = 4` and `l(u1v2) = 2q`.
Let `χ : A_{K_q} -> Z` be `χ(u1) = χ(u2) = 1`, `χ(v1) = χ(v2) = -1`.

All four cross edges are dead (even label `>= 4`, `χ(u) + χ(v) = 0`). So
`Liv^χ = {u1–u2} ⊔ {v1–v2}` is disconnected, while `Liv_0^χ = K_q` is connected
and every vertex is living. The Σ¹-conjecture
(`artin-sigma1-is-connected-dominant-living-subgraph`) predicts `[±χ] ∉ Σ^1`.

**Claim.** For every odd `q >= 3`:
- `[χ]` and `[-χ]` lie in `Σ^1(A_{K_q})`;
- `ker χ` is finitely generated.

So the Σ¹-conjecture for Artin groups fails for every `K_q` with `q` odd.

**The dichotomy in `q`.**
- For even `q`, the prime 2 divides every half-label `2, 2, 2, q`. By family 9 of
  `artin-sigma1-conjecture-known-families` (Escartín-Ferrer–Martínez-Pérez), the
  conjecture holds, so `[χ] ∉ Σ^1`.
- For odd `q` it fails. So along this family, `Σ^1` membership of the dead character
  is decided by the parity of `q` alone.

`q = 3` is Kochloukova's Example 7.1 (arXiv:2009.14269v1, §7), with
`s = u1, v = u2, u = v2, w = v1`. She writes: "We will show that Ker( χ) is finitely
generated though the Σ 1-Conjecture for Artin groups predicts that [ χ], [−χ] /∈
Σ 1(G), hence if this prediction holds Ker( χ) is not finitely generated but we do
not know whether this is the case." (Her first `χ` there is the induced character on
`G/G''`.)

The case `q = 3` was also found by swarm-0917-w14-z-break, as
`artin-k4-mixed-dead-character-lies-in-sigma1` on an unlanded branch. It uses a
different unit identity, and this claim was refereed independently of it. The new
content here is the shorter identity and the whole odd family.
