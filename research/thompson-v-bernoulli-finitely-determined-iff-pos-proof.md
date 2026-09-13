---
rg: 2
id: thompson-v-bernoulli-finitely-determined-iff-pos-proof
kind: route
title: POS gives an infinite supremum on V, Seward's corollary gives finite determination, and a rigid action rules it out at zero supremum
target: thompson-v-bernoulli-finitely-determined-iff-pos
requires:
  - thompson-v-has-a-rigid-free-ergodic-action
  - bernoulli-measures-not-finitely-determined-at-zero-supremum
  - seward-bernoulli-measures-finitely-determined-under-rbs
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
  - rokhlin-supremum-dichotomy-with-centralized-self-copies
  - positive-rokhlin-entropy-action-gives-positive-supremum
---

Items refer to the target. The general form is proved for `Γ`; `V` is covered by the first prerequisite and by
the dichotomy.

- **4 ⇒ 1.** Suppose POS fails. Then every free ergodic action has Rokhlin entropy `0`, so `h^Rok_sup(Γ) = 0`. `Γ`
  has a rigid free ergodic action; for `V` it is the first prerequisite. The second prerequisite then says no
  nontrivial finite-alphabet Bernoulli measure over `Γ` is finitely determined, contradicting item 4.
- **2 ⇒ 3.** Let `λ` be a probability vector on a finite set `L`, not a point mass. Theorem 1.10 in the fourth
  prerequisite gives `h_G(L^Γ, λ^Γ) = min(H(λ), ∞) = H(λ)`. Corollary 1.6 in the third prerequisite makes `λ^Γ`
  finitely determined.
- **3 ⇒ 4.** The uniform measure on two points is a nontrivial base.
- **1 ⇒ 2**, when `h^Rok_sup(Γ) ∈ {0, ∞}`. The sixth prerequisite turns POS into `h^Rok_sup(Γ) > 0`, and the
  dichotomy leaves `∞`.

For `V`, the fifth prerequisite gives `h^Rok_sup(V) ∈ {0, ∞}`. `V` contains `V_[0] × V_[1] ≅ V × V` and the
permutation groups of the `2^n` cylinders of length `n + 1` inside `[1]`, which commute with `V_[0]` and meet it
trivially (Remark 2.5 of its artifact). So the four items are equivalent for `V`.
