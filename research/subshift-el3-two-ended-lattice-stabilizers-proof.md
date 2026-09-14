---
rg: 2
id: subshift-el3-two-ended-lattice-stabilizers-proof
kind: route
title: Preserving a lattice at +∞ bounds the negative u-degrees, preserving one at −∞ bounds the positive ones, and bounded width forces local finiteness
target: subshift-el3-two-ended-lattice-stabilizers-locally-finite
requires:
  - bounded-width-subgroups-of-subshift-gl-are-locally-finite
artifacts:
  - research/artifacts/sk-exact-gx-2026-09-13-part1.md
---

Notation as in the target. Write the proof for `+`; the `−` case is the same with `u^{-1}` in place of `u`.

**Step 0 (rings).**
- In `R̂_+` the `u^k`-coefficient of `(Σf_iu^i)(Σg_ju^j)` is `Σ_{i+j=k} f_iα^i(g_j)`. This is a finite sum, since `i,j ≥ −n`, so `R̂_+` is a ring containing `R`.
- `Bu^j = u^jB` because `α` is an automorphism, so `u^jO_+ = O_+u^j`. Left multiplication by `u^j` maps `u^aO_+^3` onto `u^{a+j}O_+^3`.

**Step 1 (the action).**
- Let `g ∈ GL_3(R)` have width `w`, meaning all entries of `g` and `g^{-1}` have `u`-degrees in `[−w,w]`. Then `(u^aO_+^3)g ⊆ u^{a−w}O_+^3` and `(u^aO_+^3)g^{-1} ⊆ u^{a−w}O_+^3`.
- If `u^nO_+^3 ⊆ L ⊆ u^{-n}O_+^3`, then `u^{n+w}O_+^3 = (u^{n+w}O_+^3g^{-1})g ⊆ (u^nO_+^3)g ⊆ Lg ⊆ u^{-n-w}O_+^3`.
- `Lg` is a left `O_+`-submodule, because right multiplication is left linear.
- `Lg/u^{n+w}O_+^3` is finitely generated over `B`:
  - it is an extension of `(u^nO_+^3)g/u^{n+w}O_+^3`, a quotient of `u^nO_+^3/u^{n+2w}O_+^3`, which is free over `B` of rank `6w` (`u^{n+2w}O_+^3 ⊆ (u^{n+w}O_+^3)g^{-1}`);
  - by `Lg/(u^nO_+^3)g ≅ L/u^nO_+^3`, which is finitely generated.

**Step 2 (one end).**
- `O_+^3g ⊆ O_+^3` iff each row `e_ig ∈ O_+^3`, since `O_+^3 = ⊕ O_+e_i`. So `O_+^3g = O_+^3` iff `g, g^{-1} ∈ M_3(O_+ ∩ R) = M_3(B[u;α])`, with `B[u;α] = ⊕_{j≥0}Bu^j`.
- The constants `F_2 ⊆ B` and `u ∈ B[u;α]` give `SL_3(F_2[u]) = EL_3(F_2[u]) ≤ G_X ∩ GL_3(B[u;α])`.
- `SL_2(F_2[u]) ≤ SL_3(F_2[u])` contains a non-abelian free group. It is a nontrivial amalgam `SL_2(F_2) *_{B(F_2)} B(F_2[u])` (Nagao) with both indices at least `3` in the amalgamated subgroup, so it is non-amenable.

**Step 3 (both ends).**
- Let `g` fix `(L_+, L_-)`, where `u^nO_+^3 ⊆ L_+ ⊆ u^{-n}O_+^3` and `u^{-n}O_-^3 ⊆ L_- ⊆ u^nO_-^3`.
- From `L_+g = L_+`: `u^nO_+^3g ⊆ L_+ ⊆ u^{-n}O_+^3`. Left multiplying by `u^{-n}` gives `O_+^3g ⊆ u^{-2n}O_+^3`, so every entry of `g` has `u`-degrees `≥ −2n`.
- Applying the same to `g^{-1}`, which also fixes `L_+`: every entry of `g^{-1}` has `u`-degrees `≥ −2n`.
- From `L_-g = L_-`, symmetrically: all entries of `g` and `g^{-1}` have degrees `≤ 2n`.
- So every element of the stabilizer has width `≤ 2n`. By `bounded-width-subgroups-of-subshift-gl-are-locally-finite` the stabilizer is locally finite.
- For the standard pair, Step 2 at both ends gives `G_X ∩ GL_3(B[u;α]) ∩ GL_3(B[u^{-1};α]) = G_X ∩ GL_3(B)`.
- `GL_3(B)` is locally finite directly: finitely many matrices over `B` have entries in `F_2^P` for a finite clopen partition `P`, so they lie in the finite group `GL_3(F_2)^P`. ∎

**Model tests.**
- For `SL_3(F_2[u^{±1}])`, the pair stabilizer is `SL_3(F_2)`, finite, matching the classical two-building action.
- `e_12(u^k)` moves `(O_+^3, O_-^3)` for `k ≠ 0` and fixes `O_+^3` for `k > 0`: consistent with Steps 2–3.
- `diag(w_h,1,1)` for `h ∈ [[T]]′` of displacement `≤ d` has width `≤ d`, so the bound in Step 3 is not vacuous.
