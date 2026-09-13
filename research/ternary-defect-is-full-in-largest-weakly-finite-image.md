---
rg: 2
id: ternary-defect-is-full-in-largest-weakly-finite-image
kind: claim
title: The two-root defect generates the unit ideal of the ternary anti-central summand modulo its weakly finite reflection ideal
distinct_from:
  ternary-anti-central-summand-has-no-weakly-finite-image: that is 1 ∈ J_omega(S_-), the collapse of the whole largest weakly finite image; this is 1 ∈ J_omega(S_-) + S_- D S_-, which that claim implies and which still refutes Gottschalk at stage one.
  ternary-anti-central-kernel-unitization-not-directly-finite: that asks for a one-sided inverse pair in the unitized evaluation kernel, a defect invisible to the Leavitt evaluation; this asks that the reflection ideal be visible to the evaluation at some stage.
  ternary-anti-invariant-swap-corner-is-full: that is the corner equation, equivalent to the collapse; this is implied by it through a stage-one visible defect and is weaker in form.
artifacts:
  - research/artifacts/weakly-finite-image-defect-fullness-2026-09-12.md
---

**OPEN.** Let `G = L_(F_3)(1,2)^x`, `S_- = eps_- F_3[G]` and `D = N_23 N_12`. Let `J_omega` be the weakly finite
reflection ideal of `S_-` (`weakly-finite-reflection-ideal-detects-weakly-finite-images`). Then

    eps_- ∈ J_omega + S_- D S_-.

So `D` is full in the largest weakly finite image `W_max = S_-/J_omega`, trivially when `W_max = 0`. This is case 1 of
Lemma 5.2 of `research/artifacts/matrix-state-deficit-item-two-2026-09-12.md` for `W_max`.

**Equivalent form** (artifact Corollary 2.3, on paper, unverified).
- **Statement.** `pi(J_omega) != 0` for the Leavitt evaluation `pi : S_- -> L_(F_3)(1,2)`.
- **As a defect.** At some reflection stage, a pair with `AB ≡ I` modulo `J_(k-1)` has `pi(BA) != I`.
- **Negation.** `pi` factors through `W_max`.
- **Input.** The equivalence uses `ternary-anti-central-defect-ideal-is-the-evaluation-kernel`.

**Where it sits** (artifact Theorem 3.1, one-directional only).
- **Implied by** `ternary-anti-central-summand-has-no-weakly-finite-image` (route
  `no-weakly-finite-image-makes-defect-full`). It is also implied by the corner equation, through a stage-one visible
  defect.
- **Implies** `J_1(S_-) != 0`. So `F_3[G]` is not stably finite, and `G` is not surjunctive (route
  `defect-fullness-refutes-ternary-surjunctivity`).
- **Negation.** It maps `W_max` onto `L_(F_3)(1,2)`. That is a nontrivial weakly finite representation of `G`: it kills
  both corner routes and refutes nothing.
- **No converse** is claimed.

## Attempts

- 2026-09-12 `w7-wdw-fullness` (artifact Sections 2–5).
  - **Lemma 5.2 sharpened.** `S_-/S_- D S_- ≅ L_(F_3)(1,2)` (held OPEN). So for every quotient `W`, `W/WDW` is `0` or
    `R`, and case 2 says `pi` factors through `W`.
  - **Not decided.** Deciding this claim is a fork between a stage-one refutation and a nontrivial weakly finite
    representation. No visible defect is known at any stage, and no obstruction to one is known.
  - **Models.**
    - Locally finite `H <= G` containing `z` and the root pair: `F_3[H]` is stably finite and `pi|_H` kills `D`, so the
      `H`-analogue fails.
    - The dual natural module of `GL_3(F_3) <= G` gives a weakly finite image in which `D` is full while `J_1 = 0`. So
      fullness in a non-maximal image refutes nothing, and the claim needs both maximality and `pi`.
  - **Where it dies.**
    - A visible stage-one defect needs an exact pair over `S_-` lying over a non-invertible pair of `R`, such as
      `(s_0, t_0)`. The natural isometry lifts are left zero divisors (Attempts of
      `ternary-anti-central-summand-has-no-weakly-finite-image`).
    - Later stages need pairs that are one-sided only modulo defects already killed.
    - No mechanism.
