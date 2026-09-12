---
rg: 2
id: kazhdan-block-ideal-fell-isolation-proof
kind: route
title: Property (T) isolates each finite-dimensional block in the spectrum, so each block is an ideal of the block algebra
target: kazhdan-block-algebras-contain-their-block-ideal
requires: [stw01-extensions-preserve-qt-linearity]
artifacts:
  - research/artifacts/quasitrace-kazhdan-block-corona-2026-09-12.md
---

Full proof: `research/artifacts/quasitrace-kazhdan-block-corona-2026-09-12.md` §1.

1. **Isolation.** Suppose `σ ≺ π` with `σ` finite-dimensional and irreducible.
   Then `σ ⊗ σ̄ ≺ π ⊗ σ̄`, and `σ ⊗ σ̄` has the invariant vector `1`. By property
   (T), `π ⊗ σ̄ ≅ HS(H_σ, H_π)` has an invariant vector, which is a nonzero
   intertwiner. So `σ ⊂ π`. It follows that `σ` does not lie in the closure of
   `Ĝ ∖ {σ}`.
2. **Blocks.** The spectrum of `B` is `{π ∈ Ĝ : π ≺ ρ}` with the relative
   topology, and each `σ_j` is open in it. The ideal `J_j` of the open point is
   primitive, with faithful irreducible finite-dimensional representation, so
   `J_j ≅ M_{n_j}`. For `i ≠ j`, a nonzero `σ_i(J_j)` would force `σ_i ≅ σ_j`.
   So `J_j` is the coordinate block, and `I ⊂ B`.
3. **Corona.** A finite-dimensional irreducible representation of `B/I` is `≺ ρ`,
   hence some `σ_j` by step 1. But `σ_j` does not vanish on `J_j ⊂ I`.
4. **Quasitraces.** Let `σ` be a bounded 2-quasitrace on `I`, and
   `P_m = ⊕_{j ≤ m} 1_{n_j}`. For `a ∈ I_+`, the elements `aP_m` and `a(1 − P_m)`
   are orthogonal elements of `I`, so `σ(a) = lim_m σ(aP_m)`. On the
   finite-dimensional corners `σ` is a trace, so `σ` is additive on `I_+`. Now
   apply `stw01-extensions-preserve-qt-linearity`. The converse direction is
   pullback along the quotient map.
