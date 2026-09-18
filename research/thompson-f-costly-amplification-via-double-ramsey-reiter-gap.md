---
rg: 2
id: thompson-f-costly-amplification-via-double-ramsey-reiter-gap
kind: route
title: Prove that the Ramsey radius of F lies non-elementarily below its coarse Reiter radius, even after two compositions; the sandwich then gives ¬AMP
target: thompson-f-ramsey-amplification-needs-unbounded-tower-overhead
requires: [thompson-f-ramsey-radius-double-gap-below-reiter-radius, thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap]
---

**Route.** Assume RGAP₂ (`thompson-f-ramsey-radius-double-gap-below-reiter-radius`). Fix `D`. RGAP₂ gives an `M`
at which `CR(M)` exceeds the bound that Corollary 2 of `thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap`
derives from AMP(D). So AMP(D) fails. This holds for every `D`, which is ¬AMP.

**Why this is a decomposition and not a renaming.** The prerequisite removes the fine function `R̃` and the
precision parameter `u` entirely, and it is stated in terms of two objects of different logical shape: the Ramsey
radius (`∀E ∃ν`) and the coarse Reiter radius (`∃ν ∀E`). The sandwich also shows that the gap cannot be avoided,
since ¬AMP ⇒ RGAP₁. So any proof of ¬AMP must separate these two radii, and precision amplification is free
(`coarse-ball-invariance-gives-fine-reiter-measures`).
