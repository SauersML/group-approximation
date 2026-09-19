---
rg: 2
id: thompson-f-single-ramsey-reiter-gap-via-second-test-function-gap
kind: route
title: Show that two test functions cost more than any bounded tower over one; since the one-function radius dominates the Ramsey radius, the coarse Reiter radius escapes R as well
target: thompson-f-ramsey-radius-single-gap-below-reiter-radius
requires:
  - thompson-f-second-test-function-costs-more-than-any-tower
  - thompson-f-ramsey-radii-in-the-elementary-degree-order
---

**Route.** Assume SFG (`thompson-f-second-test-function-costs-more-than-any-tower`), that is, `CR ⋠ ψ`. Clause 3 of
`thompson-f-ramsey-radii-in-the-elementary-degree-order` gives `R ≼ ψ`. If `CR ≼ R` held, transitivity would give
`CR ≼ ψ`, a contradiction. So `CR ⋠ R`, which is RGAP₁ (clause 4). This is the implication SFG ⇒ RGAP₁ of clause 5.

**Why this is a decomposition and not a renaming.** SFG does not mention the set radius `R` at all. It compares
two fine Ramsey radii that differ only in the number of test functions (clause 2: `CR ≈ ψ_2`). It can fail on its
own, while RGAP₁ holds, exactly when ¬AMP holds and SFC holds. It fails in every group whose coarse Reiter radius is
elementary, and vacuously if `F` is not amenable. It is the second of the two disjuncts of RGAP₁. The other disjunct,
¬AMP, has its own route `thompson-f-single-ramsey-reiter-gap-via-costly-amplification`.
