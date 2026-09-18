---
rg: 2
id: thompson-f-amenable-via-single-ramsey-reiter-gap
kind: route
title: Show that the coarse Reiter radius of F escapes every bounded tower over one composition of its Ramsey function; finiteness of the Ramsey function then gives amenability
target: thompson-f-is-amenable
requires:
  - thompson-f-ramsey-radius-single-gap-below-reiter-radius
  - moore-ramsey-criterion-for-amenability
---

**Route.** Assume RGAP₁ (`thompson-f-ramsey-radius-single-gap-below-reiter-radius`). For each `E` it gives `N_E` with
`CR(N_E) > exp_E(R(exp_E(N_E)))`. A strict inequality in `[0, ∞]` has a finite right side, so
`R(exp_E(N_E)) < ∞`, and `exp_E(N_E) ≥ exp_E(1)` is unbounded in `E`. `R` is nondecreasing by the monotonicity facts in
`moore-ramsey-criterion-for-amenability`, so `R(M) < ∞` for every `M`. Every finite `A ⊆ F` lies in some ball `B_M`,
and `B_{R(M)}` is 1/2-Ramsey with respect to `A`, by monotonicity in `A`. Theorem 1.3 (2)⇒(4) gives that `F` is
amenable.

**Why this is a decomposition and not a renaming.** The prerequisite is strictly stronger than the target. It
also asserts that `R_F` is non-elementarily smaller than `CR_F`, and it fails on its own if CRE holds, whether or not
`F` is amenable. Its advantage over `thompson-f-amenable-via-costly-ramsey-amplification` is that its prerequisite
is weaker. ¬AMP implies RGAP₁ (sandwich, Corollary 3), and RGAP₁ is exactly ¬AMP ∨ SFG
(`thompson-f-ramsey-radii-in-the-elementary-degree-order`). So this route survives if Ramsey precision amplification
is cheap in `F` (AMP), provided the second test function is expensive (SFG).
