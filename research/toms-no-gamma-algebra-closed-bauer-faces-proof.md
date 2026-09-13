---
rg: 2
id: toms-no-gamma-algebra-closed-bauer-faces-proof
kind: route
title: Toms's towers are block-balanced, so central halving trivializes every closed face while uniform Gamma still fails
target: toms-no-gamma-algebra-is-trivial-on-closed-bauer-faces
requires:
  - block-balanced-towers-have-central-halving
  - central-halving-trivializes-every-closed-bauer-face-bundle
  - toms-ah-counterexample-to-uniform-gamma
artifacts:
  - research/artifacts/tw-projection-starved-bundle-faces-2026-09-12.md
---

Section 4 of the artifact (Corollary C).

1. **Central halving.** Toms's towers are block-balanced. The blocks and their ranks
   are recorded in the first prerequisite's route.
2. **Hypotheses of the second prerequisite.**
   - AH limits are nuclear.
   - `rank(q_i)` and `rank(s_i)` tend to infinity, and the maps are injective, so there is
     no finite-dimensional representation (Toms, Section 4: "it has no finite-dimensional
     representations").
3. **Separation.** The third prerequisite gives failure of uniform Γ for `B`.
4. **The infinite-dimensional face.**
   - The branch sequences `z_{i+1} = (z_i, z_i, ℓ_i)` give point masses at every stage, so
     the traces are extreme (Lemma 1 of
     `research/artifacts/tw-doubling-poulsen-and-comparison-2026-09-12.md`).
   - The map `(z_1, ℓ_1, ℓ_2, …) ↦ trace` is continuous, because stage `n` depends on
     finitely many coordinates, and injective, because `z_n` determines `ℓ_{n−1}`.
   - Compactness makes it a homeomorphism onto a closed subset of `∂_e T(A)`.
   - `Π_i CP^{j_i}` contains a product of arcs, that is, a Hilbert cube.
