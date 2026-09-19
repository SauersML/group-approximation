---
rg: 2
id: two-output-control-circle-maps-lose-rank-at-most-surplus-proof
kind: route
title: Glue coarse inverses into classes on neighbourhoods, kill cup products by vanishing top cohomology, and separate shared zero rows by level strips
target: two-output-control-circle-maps-lose-rank-at-most-surplus
requires: []
artifacts:
  - research/artifacts/two-output-control-rank-2026-09-19.md
---

Complete direct proof: Sections 2–6 of the artifact. The only inputs are classical:
partitions of unity, the vanishing of top cohomology for noncompact manifolds (Hatcher,
Prop. 3.29), and relative cup products for open covers (Hatcher, Section 3.2).

1. **Lemma N.** Control lets the coarse inverse of `g_(C_i)` be glued, by a partition of
   unity, into `psi_i: U_i -> T`, where `U_i ⊆ T^(C_i)` is an open neighbourhood of the
   image and `psi_i o g_(C_i) ≃ pi_i`.
2. **Lemma D.** If `U_i = T^2`, then `pi_i` is in the span of the control rows.
   Otherwise `H^2(U_i) = 0`, which forces `pi_i ∧ row_j = 0` for `j in C_i`, so either
   `pi_i` is in their span or both control rows are zero. Call the inputs of the second
   kind `B`.
3. **Lemma E.** Two inputs in `B` cannot share a zero control row `x_j`. The lift of
   `x_j` to `R` has level strips on which both classes vanish, because the slices of
   each `U_i` are unions of intervals. The resulting two-set open cover (Lemma L) kills
   `theta_1 ∪ theta_2`, which is a contradiction.
4. **Count.** `rank M >= |I| - |B|` and `|J| >= 2|B| + rank M`, so `rank M >= 2|I| - |J|`.
