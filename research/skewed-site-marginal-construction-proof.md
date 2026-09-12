---
rg: 2
id: skewed-site-marginal-construction-proof
kind: route
title: Anchor on one track, apply the strict automaton on the others, and recode anchored blocks greedily
target: strict-automata-give-injective-ca-with-skewed-site-marginals
requires: []
artifacts:
  - research/artifacts/finitary-generation-single-site-criterion-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

Artifact Section 2, Steps 1–5. Every ingredient is elementary:

1. compactness gives the Garden-of-Eden window and an automaton left inverse;
2. a self-separating anchor pattern on `D = Omega Omega^-1` makes anchored blocks disjoint;
3. greedy placement of the missing-pattern support into the classes of one coordinate makes that
   coordinate's law non-uniform, with deficit `c > 0`;
4. the chain rule, conditioning only on the anchor indicator, gives
   `H <= (k+1) log q + log 2 - rho k c`.

**Verification.** `w3-vf-positive` passed this route (Section 2.1–2.5 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`).
