---
rg: 2
id: fpbs-cycle-tail-gap-near-minimum-iff-cost-betti-gap
kind: claim
title: A gap for cycle tails of near-minimizing Bernoulli graphings holds exactly when cost exceeds one plus the first L2 Betti number
distinct_from:
  fpbs-graphing-cost-betti-cycle-dimension-identity: that proves c = 1 + beta_1 + z and the limit-interchange description; this proves that cheap chord insertion leaves short cycles unchanged, so a uniform gap for tau_L near the minimum is equivalent to the cost--Betti excess being positive
  fpbs-bernoulli-cycle-tail-compactness: that asserts compactness of cycle tails along some near-minimizing sequence; this is a proved equivalence that kills gap and quantization routes to it and asserts nothing about whether the tails vanish
  fpbs-reduced-circulation-tail-bounds-cost-excess: that bounds tau_L above by reduced relator circulation mass; this shows no lower gap for tau_L can hold near the minimum unless the excess is positive
artifacts:
  - research/artifacts/fpbs/docs/cycle-tail-hodge-gap-dictionary.md
  - research/artifacts/fpbs/docs/cost-cycle-structure.md
---

Let Gamma be infinite and finitely generated, b a free Bernoulli action, g = C(b) - 1 - beta_1^(2)(Gamma), and fix L >= 3. The following are equivalent: (i) g > 0; (ii) there are delta, eps > 0 such that every finite-piece graphing Phi generating R_b with c(Phi) < C(b) + eps has tau_L(Phi) outside the interval (0, delta). The engine is chord insertion: given a finite-piece graphing using elements from F, choose gamma with |gamma|_F > L and add the edges {y, gamma y} for y in a cylinder set U whose pattern forbids every other chord endpoint in the L-ball. This costs mu(U), which can be arbitrarily small, adds no simple cycle of length at most L, and so raises tau_L by exactly mu(U).

By the L-filled Hodge decomposition, tau_L(Phi) + beta_1 is the kernel dimension of partial_1^* partial_1 + partial_2 partial_2^* when every closed walk of length at most L is filled. So any argument for `fpbs-bernoulli-cycle-tail-compactness` that first proves a gap or quantization for this atom near the minimum, then concludes that small tails vanish, proves a statement equivalent to the failure of that claim. This covers integrality, bounded-denominator Atiyah rationality in Z/2 wr Gamma, and Lueck-type integer-Betti gap arguments. A valid route must instead supply a quantitative decay bound, or a selected sequence insensitive to chord insertion.

Status records an elementary written deduction over identities (3.1), (3.2) and estimates (4.1), (4.2) of the canonical artifact, not independent validation.
