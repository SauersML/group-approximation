---
rg: 2
id: artin-k4-mixed-dead-character-lies-in-sigma1
kind: claim
title: "The dead character (1,1,-1,-1) of the four-vertex Artin group K with cross labels 4,4,4,6 lies in Sigma^1, so its kernel is finitely generated"
distinct_from:
  artin-k4-dead-cut-admits-no-nonzero-dead-edge-ring: that says no ring witness exists for this cut, which only kills one method; this proves membership, so no method can prove the opposite
artifacts:
  - experiments/artin-k4-sigma1-2026-09-17/novikov_unit_identity.py
  - experiments/artin-k4-sigma1-2026-09-17/novikov_unit_identity.log
---

`A_K = <u1, u2, v1, v2 | [u1,u2], [v1,v2], (u1v1)^2 = (v1u1)^2, (u2v1)^2 = (v1u2)^2,
(u2v2)^2 = (v2u2)^2, (u1v2)^3 = (v2u1)^3>`, with `χ = (1, 1, -1, -1)`.

**Claim.** `[χ]` and `[-χ]` lie in `Σ^1(A_K)`, so `ker χ` is finitely generated.

This is the group of Kochloukova's Example 7.1 (arXiv:2009.14269, §7) under
`s = u1`, `v = u2`, `u = v2`, `w = v1`. There she proves only that the metabelian
quotient has finitely generated kernel: "We will show that Ker( χ) is finitely
generated though the Σ 1-Conjecture for Artin groups predicts that [ χ], [−χ] /∈
Σ 1(G), hence if this prediction holds Ker( χ) is not finitely generated but we do
not know whether this is the case." In that sentence the first `χ` is the induced
character of `G/G''`. The claim settles her question against the conjecture.
