---
rg: 2
id: fibonacci-words-model-balls-of-fibonacci-kazhdan-group
kind: claim
title: Fibonacci words of length N >= 2r+2 give injective product-preserving models of the r-ball of the Fibonacci simple Kazhdan group in SL_3N(F_2)
distinct_from:
  subshift-lef-models-period-below-twice-recurrence: that takes, for any minimal subshift, periodic models with the same words of length 4r+1, so N >= 4r+2 and N < 2 Rec_X(4r+1); this separates containment at length 4r+1 from equality at length 2r+1 for the Fibonacci subshift and reaches N >= 2r+2, the least length of any circular word containing all words of length 2r+1.
  finite-simple-groups-converge-to-simple-kazhdan-group: that gives marked convergence from primitive return words with no radius bound; this is the explicit radius-to-period dictionary for the Fibonacci words themselves.
artifacts:
  - research/artifacts/sk-open-3-fibonacci-models-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Route `fibonacci-words-model-balls-proof`, direct proof in the artifact §1–2.

**Setting.**
- X is the Fibonacci subshift of `a ↦ ab, b ↦ a`, and `R = LC(X,F_2) ⋊ Z` with `u f u^{-1} = f∘T^{-1}`.
- `G = EL_3(R)`, marked by the involutions `e_ij(s)`, `i ≠ j`, `s ∈ {1, u, u^{-1}, χ_{[x_0=a]}}` (adding
  `χ_{[x_0=b]}` changes nothing below).
- `B_r` is the r-ball.
- Fibonacci words: `f_1 = a`, `f_2 = ab`, `f_{k+1} = f_k f_{k-1}`.
- The model: `φ_z(Σ f_j u^j) = Σ D_z(f_j) P^j`, applied entrywise, with `P δ_n = δ_{n+1}` on `F_2^{Z/N}`.

**Statement.** Let `z = f_k`, `N = |f_k|`.
1. `z^∞` has exactly the same words as X of every length `L ≤ N-1`.
2. Every word of `z^∞` of length `≤ |f_{k+2}| - 1` occurs in X, and this length is attained.
3. If `N ≥ 2r+2`, then `φ_z` is injective on `B_r` and satisfies `φ_z(gh) = φ_z(g)φ_z(h)` for all `g, h ∈ B_r`.
   Its values lie in `SL_{3N}(F_2)`.
4. With only the easy fact that `zz` occurs in X, item 3 holds for `N ≥ 4r`.

**Consequences.**
- `B_1 → SL_15(F_2)`, `B_2, B_3 → SL_24(F_2)`, `B_4, B_5 → SL_39(F_2)`.
- In general N is the least Fibonacci number `≥ 2r+2`, which is at most `φ(2r+2)`, φ the golden ratio.
- A circular word containing all `2r+2` words of length `2r+1` has length `≥ 2r+2`. So item 3 is sharp among
  circular models with equal words of length 2r+1, up to the Fibonacci-number constraint.
- An exhaustive search over all binary circular words, for `r ≤ 8`, found no shorter admissible word. At the least
  length, the admissible words are exactly the rotations of the Fibonacci word.

**Computed, not proved** (MSI, artifact §3–4).
- Items 1–2 are sharp for `N ≤ 987`.
- On the exact balls (`|B_1| = 25`, `|B_2| = 445`, `|B_3| = 6925`), `φ_z` is already faithful at smaller N:
  - `B_1` and `B_2` are faithful in `SL_9(F_2)` via `aba`, with all pairs multiplicative;
  - `B_3` is faithful in `SL_15(F_2)` via `abaab`.
- So item 3 is a proved sufficient bound, not the true faithfulness threshold.

**Kazhdan constant** (artifact §5, from the page image of EJZ arXiv:0809.4095 (6.2)): with `d = 3` generators
`u, u^{-1}, χ_{[x_0=a]}`, the 24 involutions have `κ(G, Σ_24) > 1/691`. The same holds for every `Σ_24`-marked model.
