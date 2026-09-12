---
rg: 2
id: sp21-pro-p-kernel-invisible-to-local-linear-reps-proof
kind: route
title: Positive characteristic by finiteness of images, residue characteristic away from p by pro-l congruence subgroups, residue characteristic p by the Theorem A argument on the graph of the representation
target: sp21-pro-p-kernel-invisible-to-local-linear-reps
requires:
  - sp21-lattice-positive-characteristic-images-finite
artifacts:
  - research/artifacts/sp21-torsion-growth-certificate-shape-2026-09-12.md
  - research/artifacts/hyperbolic-rf-pro-p-2026-09-12.md
---

Write `P = Δ̂_p`, `π: P ->> Δ̄_p` and `N = ker π`. Continuity of `ρ` and density of
`Δ` give `ρ(P) = closure(ρ(Δ))`.

1. **`char F > 0`.**
   - `Δ` is a cocompact lattice in `Sp(n,1)`, so `ρ|_Δ` has finite image by
     `sp21-lattice-positive-characteristic-images-finite`.
   - `ρ(P)` is the closure of a finite set, hence finite, and so is `ρ(N)`.
2. **`F ⊇ Q_ℓ` finite, `ℓ != p`.**
   - `ρ(P)` is a compact subgroup of `GL_m(F)`. After conjugation it lies in
     `GL_m(O_F)`, whose principal congruence subgroup `K_1` is pro-ℓ and open.
   - `ρ(P) ∩ K_1` is both pro-p and pro-ℓ, hence trivial. So `ρ(P)` embeds in
     `GL_m(O_F)/K_1`, which is finite.
3. **`F ⊇ Q_p` finite.**
   - `ρ(P)` is a closed pro-p subgroup of `GL_m(F)`, hence p-adic analytic of
     finite rank.
   - Let `P_2 <= Δ̄_p × ρ(P)` be the image of `(π, ρ)`. It is a finite-rank pro-p
     group, `Δ` embeds in it densely, and `pr_1: P_2 ->> Δ̄_p` restricts to the
     identity on `Δ`.
   - Theorem A (⇒) in `research/artifacts/hyperbolic-rf-pro-p-2026-09-12.md` uses
     of `(P, π_Δ)` only three things: finite rank, density of `Δ`, and a
     continuous surjection onto `Δ̄_p` extending the congruence map. The same
     steps apply to `(P_2, pr_1)`:
     - Step 1: (T) makes the Lie algebra perfect.
     - Step 2: superrigidity and first-cohomology vanishing make it semisimple.
     - Step 3: the kernel ideal vanishes.
   - So `ker(pr_1)` is finite. It equals `{(1, ρ(n)) : n ∈ N}`, which is
     isomorphic to `ρ(N)`. ∎

**Trust surface.** Case 3 inherits Theorem A's inputs, as audited in
`research/artifacts/review-backlog-2-2026-09-12.md` §14 (PASS, conditional on (SR)):
- **(SR)** Margulis's arbitrary-field superrigidity, stated for every field of
  characteristic 0 with no boundedness hypothesis (Corlette and Gromov–Schoen, then
  Margulis's global deduction; not re-read).
  - Step 3 of Theorem A applies (SR) to a representation with bounded image in a
    p-adic group, so it needs the no-boundedness form.
  - The same holds for `(P_2, pr_1)`: the adjoint image of an open uniform subgroup
    of `P_2` is again compact.
- **(V)** Raghunathan's vanishing theorem plus (T).

Case 2 uses no superrigidity. Case 1 uses only
`sp21-lattice-positive-characteristic-images-finite`.
