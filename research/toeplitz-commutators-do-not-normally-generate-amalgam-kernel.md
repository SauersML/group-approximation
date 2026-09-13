---
rg: 2
id: toeplitz-commutators-do-not-normally-generate-amalgam-kernel
kind: claim
title: The Toeplitz commutators and their Weyl conjugates do not normally generate the Jacobson half-amalgam kernel
distinct_from:
  one-opposite-steinberg-relator-does-not-close-laurent-cycle: that separates the positive coordinate word from the normal closure of the negative one in a finite Laurent model; this separates them inside the Jacobson half-amalgam, using E as the model, and shows that every normal generating set of the kernel needs a letter from the finitary kernel.
  jacobson-el3-amalgam-kernel-is-the-laurent-cone-kernel: that describes the kernel; this answers the normal-generation question it raises.
artifacts:
  - research/artifacts/jacobson-el3-presentation-and-amalgam-kernel-2026-09-12.md
---

**OPEN** (candidate proof in artifact Section 2, Corollary 2.4; verification requested from `w4-vf-gate`).

Notation as in `jacobson-el3-amalgam-kernel-is-the-laurent-cone-kernel`.

1. Let `X ⊆ N ∩ U` be any set of words in the cone letters. For example, `X` can be the Toeplitz commutators
   `[x_ij(T), x_jk(S)] x_ik(1)` over all distinct `i, j, k`. Then `<<X>>_P ⊆ ker q`.
2. The head relator `R_Q = x_13(Q) [x_12(S), x_23(T)] x_13(1)` lies in `N` but not in `<<X>>_P`.
3. `N = <<ker q ∪ {R_Q}>>_P`, and `N/(N ∩ U) ≅ L`.

**Answer to the directive question.** No. `E` is not the amalgam modulo the Toeplitz commutators and their Weyl
conjugates. It is the amalgam modulo the head relator together with `ker q`.

**Proof idea.**
- `L` centralizes `N`, so normal closures of subsets of `N ∩ U` stay inside `U`.
- `R_Q` projects to `ρ_+`, whose image in `E` is the head, so `R_Q` is not in `U`.
- Simplicity of `L` gives point 3.

**Not claimed.** Whether `ker q` is the normal closure in `U` of the Toeplitz commutators.

## Attempts

* **Centralizer argument (w7-el3j-presentation, 2026-09-12).** Candidate proof in artifact Corollary 2.4. Awaiting
  `w4-vf-gate`.
