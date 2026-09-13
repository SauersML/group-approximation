---
rg: 2
id: every-artin-dead-cut-admits-a-commutative-ring-witness
kind: claim
title: "Refuted approach: every disconnected living subgraph of an Artin group admits a commutative dead-edge ring, as finite abelian twists would require"
refuted_by: [artin-346-commutative-rings-miss-the-dead-cut]
distinct_from:
  every-artin-dead-cut-admits-a-nonzero-dead-edge-ring: that allows non-commutative rings and is refuted only by a four-vertex graph; this asks for commutative rings, the finite abelian twist method of Escartin-Ferrer, and already fails on a triangle
---

Statement (refuted). For every Artin group `A_Γ` and every discrete `χ` with `Liv_0^χ`
connected and dominant and `Liv^χ` disconnected, some admissible vertex partition
admits a nonzero COMMUTATIVE ring `R` and `ρ : A_Γ -> R^×` killing every cross
dead-edge sum.

This is the mechanism behind Escartín-Ferrer's families: prime `p`, balanced
(arXiv:2501.08692v3, Theorem 4.4 with `R = C`).

## Attempts

- 2026-09-13: refuted by the triangle `A(3,4,6)` with `χ = (1,-1,-1)`
  (`artin-346-commutative-rings-miss-the-dead-cut`), where the conjecture is true by
  Almeida–Kochloukova and is detected by a rank-two representation. The route
  `artin-sigma1-conjecture-via-commutative-ring-witnesses` is dead.
