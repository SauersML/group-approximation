---
rg: 2
id: frobenius-support-idempotents-boolean-realization-proof
kind: route
title: Odd-order group sums are idempotents; the joint decomposition under two commuting Frobenius groups plus simplicity of corner groups gives the dichotomy, and additivity follows from diagonal fixed spaces
target: frobenius-support-idempotents-give-boolean-realization
requires:
  - subshift-elementary-group-rigid-supports-are-mutual-centralizers
  - infinite-simple-kazhdan-hyperlinear-group
artifacts:
  - research/artifacts/sk-normalizer-recognition-2026-09-14-part1.md
---

The full derivation is in `research/artifacts/sk-normalizer-recognition-2026-09-14-part1.md` §§1–3.

- **Item 1.**
  - `|F21| = 21` is odd, so `P = Σ_{k∈K} k` satisfies `P² = P` and `kP = Pk = P`.
  - `PM = Fix(K)` and `(I−P)M = [M,K]`, since `Σ_k(k−I) = P − I`.
  - X-side: `Σ_{q∈F21} q_V = e_{X∖V}I + e_V·(projection onto Fix_{F21}(F_2^3)) = e_{X∖V}I`, because a Singer cycle has no
    nonzero fixed vector.
  - Faithfulness of `M` gives `S_V ≠ 0`; disjoint supports commute.
- **Item 2.** `E3_U` commutes with `F21_{X∖U} ≤ G_{X∖U}` by C2, so `α(E3_U)` preserves `S_{X∖U}M`.
  - The commuting idempotents `S_U, S_{X∖U}` split `M` into four pieces. `α(F21_U)` is fixed-point free exactly on the
    pieces inside `S_UM`.
  - (⇒) Trivial action forces `S_US_{X∖U}M ⊆ Fix ∩ [M, α(F21_U)] = 0`.
  - (⇐) `α(F21_U)` then acts trivially on `S_{X∖U}M`. The kernel of the action is normal in the simple group
    `α(E3_U)`, because `e_UR_Xe_U ≅ LC(U,F_2)⋊_{T_U}Z` with `T_U` a minimal subshift, and Theorem 1 of the note applies
    through `infinite-simple-kazhdan-hyperlinear-group`. So the kernel is everything.
- **Item 3.** Under (O), the diagonal copy `α(F21_{V⊔W})` has fixed space `Fix(α(F21_V)) ∩ Fix(α(F21_W))`, so
  `S_{V⊔W} = S_V + S_W`.
  - (O′) gives complements, and expanding over the pieces `V∩W`, `V∖W`, `W∖V` gives meets.
  - Item 2 with (O) puts `α(E3_V)` in the `S_V`-corner.
  - `L_X = L_V × L_{X∖V}` with `L_V ≤ E3_V`, so `α(L_X)` commutes with each `S_V`.

**Model tests.**
- `α = id` gives `S_V = e_VI`.
- `α = inn(diag(u,1,1))` gives the non-scalar `S_V = diag(e_{TV},e_V,e_V)`, consistent with recognition only up to
  `N_Y`.
- The natural ⊕ trivial fake fails (O′).
