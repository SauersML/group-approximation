---
rg: 2
id: fpbs-cycle-tail-gap-near-minimum-iff-cost-betti-gap-proof
kind: route
title: Insert cheap long chords on a pattern-isolated cylinder set and read off the tail with the cost identity
target: fpbs-cycle-tail-gap-near-minimum-iff-cost-betti-gap
requires:
  - fpbs-graphing-cost-betti-cycle-dimension-identity
artifacts:
  - research/artifacts/fpbs/docs/cycle-tail-hodge-gap-dictionary.md
---

Artifact Section 2, Lemma 2 and Theorem 3. First, the cylinder condition x_(w^-1) outside B for all words w of length at most L over F and gamma forces the only chord endpoints in the L-ball around a chord base y to be y and gamma y. Second, a short simple cycle through that chord would leave an F-chain with boundary gamma y - y supported in length at most L - 1; this is impossible, because the F-distance from y to gamma y exceeds L and boundary coefficients sum to zero on each support component. Hence Z_L is unchanged and z rises by mu(U) through c = 1 + beta_1 + z. For (i) implies (ii), estimate (4.2), tau_L >= g - (L-1) eps, gives delta = g/2. For (ii) implies (i), when g = 0 estimate (3.2) gives near-minimizers with tau_L <= z = eps small, and chord insertion moves tau_L into (0, delta) at cost below eps. The prerequisite identity is the only imported L2 input; Section 1 of the canonical artifact supplies finite-piece near-minimizers.
