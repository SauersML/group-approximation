---
rg: 2
id: triangular-piece-lifts-need-non-directly-finite-shift-group
kind: claim
title: A lift of s0 in idempotent pieces with an acyclic defect graph forces a non-directly-finite shift group, and finite supports need a cycle of partial conjugations
distinct_from:
  finite-subgroup-idempotent-ideals-admit-no-proper-group-shift: that treats one idempotent and one group element; this treats any number of pieces and relative shifts, where the transfer group can be two-dimensional
  two-piece-s0-lifts-telescope-to-a-corner: that gives the exact unit criterion for two pieces; this is a necessary condition for the triangular case with any number of pieces
artifacts:
  - research/artifacts/triangular-lift-hnn-transfer-2026-09-12.md
---

**ESTABLISHED** by route `triangular-piece-lift-shift-group-transfer-proof`. Re-derivation requested from
`w4-vf-linear-b`.

Let `A = F_2[R^x]`, and take artifact Data 4.0:
- a complete prefix code `beta_1..beta_m`;
- orthogonal idempotents `E_i` summing to `1`, all in `F_2[K]` for one subgroup `K`, with `pi(E_i) = P_(beta_i)`;
- units `g_i` carrying cylinder `beta_i` onto `0 beta_i`, with `h_ij = g_i^(-1) g_j`.

Put `X_ij = E_i[h_ij]E_j` and `Z = {(i,j) : i != j, X_ij = 0}`. Suppose the digraph of nonzero `X_ij` is acyclic, so
`a = sum [g_i]E_i` is a left-invertible lift of `s0`.

**Theorem.** Let `H` be any group mapping to `R^x`, with `K -> H` lifting the inclusion and `t_i -> g_i`, in which
`t_i^(-1) t_j` conjugates `D_ij = K ∩ h_ij K h_ij^(-1)` as `h_ij` does, for every `(i,j)` in `Z`. Then `F_2[H]` is not
directly finite. This applies to the universal such `H_Z`.

**Corollary.** Suppose `K` is finite. Form the graph `Gamma` on `{1..m}` with an edge `{i,j}` whenever `(i,j)` or
`(j,i)` lies in `Z` and `D_ij != 1`. If `Gamma` is a forest, `H_Z` is virtually free, and no such lift exists. So a
finite-support witness needs `m >= 3`, a cycle in `Gamma`, and a non-sofic finitely presented group `H_Z` built from
`K`, the letters, and one 2-cell per cycle.

For `m = 2` the corollary recovers `finite-support-triangular-two-piece-s0-lifts-do-not-exist`. Artifact Section 4.

**Sharpening** (artifact Theorem 5.1, suggested by lane `w4-kap-join`).
- **Statement.** It is enough that `H` has one homomorphism into a sofic group that is injective on the finite ball
  `S = {1} ∪ supp(x)·supp(c)`, where `x = sum [t_i]E_i` and `c` is its left inverse in `k[H]`.
- **Why.** `cx = 1` passes to the image, where it becomes two-sided by Elek–Szabó. `1 - xc` is supported on `S`, so it
  vanishes upstairs. Then `a` would be invertible.
- **Consequence.** A surviving candidate needs a finite configuration of partial conjugations that no sofic group
  realizes faithfully on `S`. A finite group realizing it certifies the candidate dead.
