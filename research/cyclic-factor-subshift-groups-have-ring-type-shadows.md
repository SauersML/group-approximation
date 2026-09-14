---
rg: 2
id: cyclic-factor-subshift-groups-have-ring-type-shadows
kind: claim
title: If X has a finite cyclic factor of order m ≥ 2, every finite simple approximant of G_X is eventually PSL_3md(F_2^f) induced by ring models
distinct_from:
  subshift-group-finite-simple-shadows-are-ring-models: that is the rank-three type question for every infinite minimal X; this settles it for X with a nontrivial finite cyclic factor, leaving exactly the totally minimal case open.
  el-rank-four-finite-simple-shadows-are-ring-models: that is type rigidity for EL_N with N ≥ 4 over any f.g. ring; this applies it to the note's rank-three G_X by rewriting G_X as EL_3m over the induced subshift.
artifacts:
  - research/artifacts/sk-rank3-shadows-2026-09-14.md
---

**ESTABLISHED (unreviewed)** by `cyclic-factor-subshift-groups-have-ring-type-shadows-proof`.

**Statement.** Let `X` be an infinite minimal subshift with a finite cyclic factor of order `m ≥ 2`, `U` a cyclic piece
(`X = ⊔_(i<m) T^iU`), and `X_1 = (U, T^m|_U)`. Let `(Q_k, T_k) → (G_X, T)` for a finite marking `T`, with `Q_k` finite simple.
Then for all large `k`:
- `Q_k ≅ PSL_(3md_k)(F_(2^(f_k)))`, with `d_k → ∞`;
- after rewriting `T` into the elementary marking of `EL_(3m)(R_(X_1)) = G_X`, the marking is induced by a surjective ring
  map `ρ_k: F_1 → M_(d_k)(F_(2^(f_k)))`, where `F_1` is free on generators of `R_(X_1)`;
- the natural dimension is divisible by `3m·c` for each `c ∈ Cyc(X_1)`.

**Scope.** This covers Thue–Morse, period doubling and every Toeplitz subshift. The totally minimal case (Sturmian,
Fibonacci) stays open.

## Review
- **sk-verify-19 PASS-WITH-FIXES (2026-09-14, `research/artifacts/sk-verify-19-2026-09-14-part2.md` §1):** re-derived:
  - the cyclic partition; the induced system is first-return, hence minimal, and a subshift by m-block coding;
  - G_X = EL_{3m}(R_{X_1});
  - change of marking preserves convergence, so [D] with N = 3m ≥ 6 applies; d_k → ∞; characteristic 2;
  - divisibility by [E].
  - Fixes: (F1) "for each c ∈ Cyc(X_1), eventually 3m·c divides the natural dimension" (the "large k" depends on c); (F2) the artifact's "Cyc(X) = m·Cyc(X_1)" is unused; use "contains".
