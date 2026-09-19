---
rg: 2
id: thompson-f-single-ramsey-reiter-gap-via-costly-amplification
kind: route
title: Show that Ramsey precision amplification in F costs more than any bounded tower; Corollary 3 of the sandwich then separates the coarse Reiter radius from R
target: thompson-f-ramsey-radius-single-gap-below-reiter-radius
requires:
  - thompson-f-ramsey-amplification-needs-unbounded-tower-overhead
  - thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap
---

**Route.** Assume ¬AMP (`thompson-f-ramsey-amplification-needs-unbounded-tower-overhead`). Fix `E` and put
`D = E + 3`. AMP(D) fails, so by Corollary 1 of `thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap` CRE(E)
fails: some `N` has `CR(N) > exp_E(R(exp_E(N)))`. This holds for every `E`, which is RGAP₁. This is the implication
¬AMP ⇒ RGAP₁ of Corollary 3.

**Why this is a decomposition and not a renaming.** ¬AMP is a statement about the fine function `R̃` and the precision
parameter, while RGAP₁ is not. ¬AMP can fail on its own, with RGAP₁ true, exactly when AMP and SFG both hold
(`thompson-f-ramsey-radii-in-the-elementary-degree-order`, clause 5). Together with
`thompson-f-single-ramsey-reiter-gap-via-second-test-function-gap`, this route covers both disjuncts of RGAP₁.
