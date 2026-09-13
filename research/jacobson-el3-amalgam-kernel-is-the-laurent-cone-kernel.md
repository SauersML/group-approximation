---
rg: 2
id: jacobson-el3-amalgam-kernel-is-the-laurent-cone-kernel
kind: claim
title: The Jacobson half-amalgam kernel is the Laurent cone-amalgam kernel, and the head is the image of the positive coordinate word
distinct_from:
  jacobson-one-sided-symbol-preimages-are-lef: that shows the halves are LEF and that E is a proper quotient of their amalgam; this computes the kernel of that quotient.
  one-opposite-steinberg-relator-does-not-close-laurent-cycle: that separates the two coordinate words over a Laurent ring with a finite model; this identifies the Jacobson half-amalgam kernel with the Laurent cone kernel and computes its image in the finitary kernel.
  leavitt-amalgam-microstates-have-unrepairable-kernel: that uses one nontrivial kernel element of a Leavitt amalgam quotient to rule out perturbative repair; this describes the whole kernel for the Jacobson halves.
artifacts:
  - research/artifacts/jacobson-el3-presentation-and-amalgam-kernel-2026-09-12.md
---

**OPEN** (candidate proof in artifact Section 2; verification requested from `w4-vf-gate`).

Let `J = F_2<S,T | TS=1>`, `E = EL_3(J)`, and let `L` be the kernel of the symbol `π : E -> SL_3(F_2[z^(±1)])`.
- The cones are `G_+ = EL_3(F_2[S])`, `G_- = EL_3(F_2[T])` and `G_0 = SL_3(F_2)`.
- The halves are `H_± = L ⋊ G_±` and `H_0 = L ⋊ G_0`, with `P = H_+ *_(H_0) H_-` and `N = ker(P -> E)`.
- The cone amalgam is `U = G_+ *_(G_0) G_-`, with canonical `q : U -> E` and `K_Λ = ker(π q)`.

1. `L` is normal in `P`, and `P = L ⋊ U`.
2. `N ∩ L = 1` and `[N, L] = 1`. The projection `P -> U` maps `N` isomorphically onto `K_Λ`, with inverse
   `u -> q(u)^(-1) u`.
3. `q` is onto, so `E ≅ U / ker q`. It restricts to a surjection `ℓ : K_Λ -> L` with kernel `ker q = N ∩ U`.
4. `ℓ` kills the Toeplitz word `ρ_- = [x_12(T), x_23(S)] x_13(1)`, and sends `ρ_+ = [x_12(S), x_23(T)] x_13(1)` to the
   head `x_13(Q)`.

**Payoff.** `N` does not depend on `J`; the ring enters only through `ℓ`. The directive "any obstruction lives in `N`"
sharpens: an obstruction is a property of the normal subgroup `ker q` of `U`, equivalently of `ℓ`, and not of `N` as an
abstract group (`jacobson-el3-amalgam-kernel-is-residually-finite`).

## Attempts

* **Semidirect splitting of the half-amalgam (w7-el3j-presentation, 2026-09-12).** Candidate proof in artifact
  Section 2, Propositions 2.1–2.2. Awaiting `w4-vf-gate`.
