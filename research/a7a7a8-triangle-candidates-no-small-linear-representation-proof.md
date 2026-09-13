---
rg: 2
id: a7a7a8-triangle-candidates-no-small-linear-representation-proof
kind: route
title: Case analysis of faithful vertex modules, reduction of the char-2 4-type to dimension 5, and trace-ideal Gröbner certificates
target: a7a7a8-triangle-candidates-no-small-linear-representation
requires: [a7a7a8-triangle-candidates-no-4dim-char2-representation]
artifacts: [research/artifacts/hyperbolic-triangle-linear-search-2026-09-13.md, experiments/hyperbolic-triangle-search/linZ.py, experiments/hyperbolic-triangle-search/linZ_c1.out, experiments/hyperbolic-triangle-search/linZ_c234.out, experiments/hyperbolic-triangle-search/linZ_cal.out, experiments/hyperbolic-triangle-search/linD.py, experiments/hyperbolic-triangle-search/linD_d6c2_cands.out, experiments/hyperbolic-triangle-search/lin5.py, experiments/hyperbolic-triangle-search/lin5_cands.out, experiments/hyperbolic-triangle-search/lin5_cal.out]
---

The full argument is in `research/artifacts/hyperbolic-triangle-linear-search-2026-09-13.md` §§2, 5 and 6.

**Step 0 (reduction).** Replace `K` by its algebraic closure. A nontrivial `φ` is injective on the
simple vertex groups.

**Step 1: `p ∉ {2, 7}`.**
- `A_8` has no faithful module of dimension at most 6. In dimension 7 the faithful modules are the heart `7` for `A_8` and
  `F^7 = 1 ⊕ 6` for `A_7`. Semisimplicity follows from `H^1(A_7, F_p^7) = H^1(A_6, F_p) = 0`.
- Integral model: `t_0 = φ(q)^{e_1}` is a regular 7-cycle matrix, `C(t_0)` is the circulants, and
  `β = h β_1 h^{-1}` with `β_1 = π β_0 π^{-1}` integral. The traces of 117 words in `(u, v)` are equated with the heart.
- The strong Gröbner basis over `Z` is `[1]` for all four candidates (`linZ_c1.out`, `linZ_c234.out`). A solvable
  calibration returns neither `[1]` nor an integer (`linZ_cal.out`).

**Step 2: `p = 7`.**
- The `A_8`-module is `7`, on which a 7-element acts as `J_7`.
- `φ(p)` and `φ(r)` are 7-elements of `φ(C)`, so their Jordan type is `J_7`. Therefore `A` and `B` act by modules whose
  restriction to a Sylow 7-subgroup is free.
- By Higman's criterion these modules are projective. A projective 7-dimensional module with
  factors `{1, 5, 1}` is the projective cover of the trivial module, which is the permutation module
  `F_7[A_7/A_6]`.
- `t_0` is regular unipotent, so `C(t_0)` is again the circulants, and the certificate of Step 1 applies.

**Step 3: `p = 2`.**
- **Composition types.**
  - Faithful modules of dimension at most 7 have composition factors `{6, 1^k}` or `{4^{(*)}, 1^k}`.
  - The eigenvalue multiset of a 7-element determines the type, and each edge generator is shared by two vertices. So the
    type is uniform around the triangle.
- **Type 6.**
  - `d = 6` means the irreducible `6`, where the trace ideal is `(1)` (`linD_d6c2_cands.out`).
  - `d = 7` means `A` and `B` act as `6 ⊕ 1`, semisimple since `H^1(A_7, 6) = 0` by Shapiro, while `C` may be any module with factors `{6, 1}`.
    The trace equations are necessary for all of these, and the certificate of Step 1 applies.
- **Type 4, semisimplicity.** `H^1(A_7, 4) = H^1(A_7, 4*) = 0`: every `A_7` in `AGL_4(2)` fixes a point, since
  16 is not a sum of the indices 7, 15, 21, … of proper subgroups. Also `H^1(A_8, 4) = 0` (recalled) and `H^1(X, F_2) = 0`.
  So `V|X = 4^{(*)} ⊕ 1^{d−4}`.
- **Type 4, the subspaces.** `W_X = [V, X]` has dimension 4 and `W_A ∩ W_C ⊇ [V,p]` has dimension 3.
  - If two of the `W_X` coincide, all three do. Then `φ` lives on `W`, and dimension 4 is excluded by the required claim.
  - Otherwise `U = W_A + W_B + W_C` has dimension 5, is invariant, and carries modules `4 ⊕ 1`.
- **Type 4, dimension 5.**
  - In the eigenbasis `C(t) = GL_2 × T^3`, with trace equations against `4^{(*)} ⊕ 1`.
  - For `G_2` and `G_4` no type triple is consistent. For `G_1` and `G_3` the consistent ones give
    `(1)` (`lin5_cands.out`).
  - On the literal triples, solvable controls give 3-dimensional ideals (`lin5_cal.out`).

**Trusted inputs.**
- Singular.
- The small modular irreducible degrees of `A_7` and `A_8` for `p = 2, 3, 5, 7`.
- `H^1(L_4(2), F_2^4) = 0`.
