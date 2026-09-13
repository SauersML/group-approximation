---
rg: 2
id: depth-monotone-units-carry-weakly-finite-nonzero-defect
kind: claim
title: Sofic unit subgroups containing minus one and the standard frame, including the depth-monotone ones with omega(0) at most omega(1), have weakly finite ternary representations sending minus one to minus one with nonzero two-root defect
distinct_from:
  depth-monotone-configurations-cannot-force-ternary-minus-one: that gives weakly finite models of weighted unit groups with z -> -1, all of which kill D; this gives models with z -> -1 and D != 0 on the same groups, so their relations cannot force the defect form either.
  anti-central-sofic-data-cannot-force-defect-submultiplicativity: that realizes anti-central regular ranks with cylinder defects of rank 5/9 on sofic subgroups; this is the weakly finite form for the standard frame read directly from the group algebra, plus an explicit tensor-cube model on H^omega_<= that uses no soficity and no rank function.
  ternary-weakly-finite-representations-kill-two-root-defect: that asks D = 0 in every weakly finite representation of G; this realizes D != 0 on every sofic subgroup containing z and the frame, so a proof has to use relations outside all of them.
artifacts:
  - research/artifacts/four-transvection-escape-set-2026-09-12.md
---

**OPEN** (proved on paper, artifact Section 4 and Lemma 3.1; held OPEN until `w4-vf-gate` re-derives it).

**Statement.** Let `G = L_(F_3)(1,2)^x`, `z = -1`, `ε_- = 2(1 - [z])`, `x_12(1) = 1 + s_0 t_10`,
`x_23(1) = 1 + s_10 t_11`, and `D_ρ = (ρ(x_23(1)) - 1)(ρ(x_12(1)) - 1)`.
1. If `Γ_0 <= G` is sofic and contains `z`, `x_12(1)` and `x_23(1)`, then `g -> ε_- g` is a homomorphism into the
   units of the weakly finite corner `ε_- F_3[Γ_0]`, with `z -> -1` and `D != 0`.
2. For every weight with `ω(0) <= ω(1)`, `H^ω_≤` satisfies the hypotheses of 1. In particular `H^1_≤` does.
3. Explicitly, `g -> [((π(g)|_(F_k))^(⊗3))_k]` is a homomorphism from `H^ω_≤` into the units of the stably finite
   algebra `∏_k End(F_k^(⊗3)) / ⊕_k End(F_k^(⊗3))`, with `z -> -1` and `D != 0`.
4. Every model that restricts a unital algebra homomorphism from the span of the group kills `D`, because
   `s_10 t_11 s_0 t_10 = 0`.

**Consequence.** The defect form is firewalled on every depth-monotone unit group that contains the standard frame.
This answers the second question of `w6-mismatch-c3`. The depth-monotone models kill `D` only because they are
algebra homomorphisms. The tensor cube is not additive, and it keeps the sign because the power is odd.

**Scope.** On `H^ω_≥`, compose with `g -> (g*)^(-1)` and use the image frame. Subgroups not known to be sofic are not
covered. The smallest one known to escape every algebra-level model is `Γ_5`, in
`four-transvections-and-x23-force-defect-vanishing`.
