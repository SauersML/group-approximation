---
rg: 2
id: v-rank-functions-split-as-augmentation-plus-reduced
kind: claim
title: Every rank function on a group algebra of Thompson's V is phi_V times the augmentation rank plus a rank function with fixed rank zero
distinct_from:
  v-rank-functions-are-trivial-plus-regular-on-cylinder-groups: that computes a rank function on each finite subgroup from phi_V; this splits the whole rank function on F[V] globally, and does not use that claim.
  v-rank-torsion-constant-equals-global-fixed-rank: that identifies the torsion constant with the fixed rank; this applies it to rk and to its transpose to cut off the trivial part as a two-sided summand.
artifacts:
  - research/artifacts/thompson-v-rank-functions-split-off-augmentation-2026-09-12.md
---

**OPEN.** The candidate proof is Section 1 of the artifact. It is held open until `w3-vf-linear` re-derives it.

**Setting.** `F` is any field, `rk` a Sylvester matrix rank function on `F[V]`, `phi_V = 1 - rk col(1 - [s] : s in S)`
for a finite generating set `S`, and `rk_aug(A) = rank_F eps(A)`.

**Claim.** If `phi_V < 1`, then `rk_0 = (rk - phi_V rk_aug)/(1 - phi_V)` is a Sylvester matrix rank function on
`F[V]`, and `phi_V(rk_0) = 0`.

**Consequences** (artifact Sections 1.5 and 2).
- **Convex structure.** The rank functions on `F[V]` form the join of the point `rk_aug` and the face
  `P_0 = {phi_V = 0}`, and the decomposition is unique.
- **Models.** A model with `0 < phi_V < 1` is the direct sum of the trivial model and a model with `phi_V = 0` whose
  rank function is `rk_0`. The fixed idempotent is the rank limit of averaging idempotents and is invariant on both
  sides. This replaces the [matricial] step of Corollary 1.3(5) in
  `research/artifacts/thompson-v-rank-models-fixed-rank-and-wandering-freeness-2026-09-12.md`.
- **Gates.**
  - `thompson-v-has-no-nontrivial-f2-rank-model` is equivalent to: no characteristic-two model has `phi_V = 0`.
  - `thompson-v-ternary-rank-functions-are-augmentation` is equivalent to: no rank function on `F_3[V]` has `phi_V = 0`.
- **What it doesn't do.** It decides neither gate.

## Attempts

- **Candidate proof** (w7-v-rank-split, artifact Section 1).
  - **Two-sided almost invariance.** For a clopen-cycle group `P`, `rk col((1 - [g_i]) e_P) <= rk(e_P) - phi_V` follows
    from (S5) alone, because `(1 - [g]) e_P (1 - e_P) = 0` needs no commutation. The row bound is the same bound for
    the transposed rank function `rk*(A) = rk((A*)^T)`, whose fixed rank is also the torsion constant.
  - **Cutting.** `rk(A) = rk(e_P) rank eps(A) + rk((1 - e_P) A (1 - e_P))` up to `2 |supp A| n (1 - phi_V)/|P|`. The
    compressions are multiplicative up to the same error.
  - **Axioms.** Products and upper-triangular blocks pass to the limit of the compressions.
  - **Where it stops.** It decides neither gate. After a PASS, add route `v-rank-split-augmentation-plus-reduced-proof`
    requiring `v-rank-torsion-constant-equals-global-fixed-rank` and `v-rank-models-are-trivial-plus-free-on-odd-cycle-trees`.
- **Not formal** (artifact Section 1.4).
  - **Example.** Take `Z` through the Jordan block `[[1, 1], [0, 1]]`, or `Z/2` in characteristic two on its regular
    module. Then `phi = 1/2`.
  - **What breaks.** `rk_0` fails the triangular axiom on `[[y, 1], [0, y]]` with `y = 1 - [g]`: `rk_0 = 1 < 2`.
  - **Why `V` escapes.** Lemma 1.2 excludes a Jordan block coupling the trivial part to the rest.
