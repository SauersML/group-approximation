---
rg: 2
id: finite-support-multi-piece-triangular-s0-lift-exists
kind: claim
title: Some lift of s0 in three or more finite-subgroup idempotent pieces has an acyclic off-diagonal defect graph
distinct_from:
  two-piece-s0-lift-with-triangular-defect-exists: that is the two-piece case, which is dead on finite supports; this allows three or more pieces, where the transfer group can carry a genuine two-dimensional cycle
  finite-support-triangular-two-piece-s0-lifts-do-not-exist: that refutes the two-piece triangular case on finite supports; this is the multi-piece shape that refutation does not reach
artifacts:
  - research/artifacts/triangular-lift-hnn-transfer-2026-09-12.md
---

Let `A = F_2[R^x]` with `R = L_(F_2)(1,2)` and evaluation `pi`. There exist:
- a complete prefix code `beta_1, ..., beta_m` with `m >= 3`;
- orthogonal idempotents `E_1, ..., E_m` of `A` summing to `1`, all supported on one finite subgroup `K` of `R^x`, with
  `pi(E_i) = P_(beta_i)`;
- units `g_i` in `R^x` with `g_i s_(beta_i) = s_0 s_(beta_i)` and `g_i P_(beta_i) g_i^(-1) = P_(0 beta_i)`;

such that the digraph `{(i,j) : E_i[g_i^(-1) g_j]E_j != 0}` is acyclic.

By artifact Lemma 4.1, `a = sum_i [g_i]E_i` is then a left-invertible lift of `s0`, witnessing
`left-invertible-lift-of-s0-in-leavitt-group-algebra`.

## Attempts

**2026-09-12, shift-group transfer (lane `w4-kap-triangular`).** Artifact Section 4.

* **Necessary: a non-directly-finite shift group** (`triangular-piece-lifts-need-non-directly-finite-shift-group`).
  - Each vanishing piece is an equation on one double coset.
  - It survives in any group in which the relative shifts `t_i^(-1) t_j` conjugate `D_ij = K ∩ h_ij K h_ij^(-1)` as
    in `R^x`.
  - In such a group, `sum [t_i]E_i` is left invertible.
* **Dead: forests.** Let `Gamma` be the graph of pairs with a vanishing piece and `D_ij != 1`. If `Gamma` is a forest,
  the shift group is a graph of finite groups, virtually free, with directly finite group algebra. Two pieces always
  give a forest.
* **Where it stops.**
  - A witness needs a cycle in `Gamma`: at least three pieces whose relative shifts each conjugate a nontrivial
    subgroup of `K` into `K`.
  - The finitely presented shift group `H_Z`, with one 2-cell per cycle, must be non-sofic.
  - No candidate `(K, beta, g_i)` has been examined. The first test is `m = 3` with `K` the depth-two constants
    `GL_4(F_2)` and `beta = (0, 10, 11)`: check whether the three relative shifts give nontrivial intersections
    `D_ij`, and whether `H_Z` is visibly sofic, for instance through a finite quotient faithful on `K` whose kernel
    acts freely on a CAT(0) 2-complex.
