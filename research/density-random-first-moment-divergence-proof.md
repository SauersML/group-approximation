---
rg: 2
id: density-random-first-moment-divergence-proof
kind: route
title: Fill relator sets with products of three conjugates of a_1^3 and use the alternating quotients of Z/3 * F_(m-1)
target: density-random-simple-quotient-first-moment-diverges
requires: []
artifacts:
  - research/artifacts/solve-hyperbolic-rf-2026-09-13.md
  - experiments/hyperbolic-rf/density_quotient_checks.py
---

Notation as in the target. Write `a = a_1`.

## Step 1: many relator words in <<a^3>>

Fix `r >= 2` and put `L = 6r + 9`. Take reduced words `x, y, z` of length `r` such that:
- none of their last letters is `a` or `a^{-1}`;
- their first letters are pairwise distinct.

Put `W(x, y, z) = x a³ x^{-1} y a³ y^{-1} z a³ z^{-1}`.

**No cancellation.** Check each junction:
- `x·a` cancels only if `x_r = a^{-1}`, and `a·x^{-1}` only if `x_r = a`;
- `x^{-1}·y` cancels only if `y_1 = x_1`, and likewise for `y, z`;
- the cyclic junction `z^{-1}·x` cancels only if `x_1 = z_1`.

So `W` is cyclically reduced of length `L`. Since `x`, `y`, `z` sit at fixed positions,
`W` is injective, and every `W` lies in `<<a³>>`.

**Counting.** Choose the first letters in order (`2m`, `2m−1`, `2m−2` ways), then the
letters `2, …, r−1` of each word (`2m−1` ways each), then each last letter, avoiding
`a`, `a^{-1}` and the inverse of the previous letter (at least `2m−3 >= 1` ways). The
set `T_0` of these words has

```text
|T_0| >= 2m(2m−1)(2m−2) ((2m−1)^(r−2) (2m−3))^3 = c_m (2m−1)^(3r),   c_m > 0.
```

Since `3r = (L−9)/2` and `d < 1/2`, there is `L_0` with `|T_0| >= k` whenever
`L >= L_0` and `L ≡ 3 (mod 6)`.

## Step 2: infinitely many simple quotients killing a^3

Let `n >= 5` be odd and `σ = (1 2 ⋯ n)`. Define `ψ_n: F_m -> Sym(n)` by `a_1 ↦ (1 2 3)`,
`a_2 ↦ σ` and `a_i ↦ 1` for `i >= 3`. Then `ψ_n(a³) = 1`.

**The image is `A_n`.**
- It lies in `A_n`, since `σ` is even for odd `n`.
- It contains `σ^j (1 2 3) σ^{-j} = (1+j, 2+j, 3+j)` for `0 <= j <= n−3`.
- Put `G_k = ⟨(1 2 3), (2 3 4), …, (k−2, k−1, k)⟩`. By induction `G_k = A_k`: first,
  `G_3 = A_3`. If `G_(k−1) = A_(k−1)`, then `A_(k−1)` fixes `k` and is transitive on
  `{1, …, k−1}`, and `(k−2, k−1, k)` sends `k` to `k−2`. So the orbit of `k` is
  `{1, …, k}` and `|G_k| >= k·|A_(k−1)| = k!/2`, with `G_k <= A_k`.

`A_n` is simple for `n >= 5`, which is classical. The kernels
`N_n = ker ψ_n` are pairwise distinct.

## Step 3: divergence

Take `L >= L_0` with `L ≡ 3 (mod 6)`, so `T_0 ⊆ <<a³>> ⊆ N_n` for every odd `n >= 5`. Then
`P[R ⊆ N_n] >= P[R ⊆ T_0] = p_0`, where:
- `p_0 = C(|T_0|, k)/C(C_L, k)` in the subset model;
- `p_0 = (|T_0|/C_L)^k` for independent choices.

In both cases `p_0 > 0` because `|T_0| >= k`, and `p_0` does not depend on `n`. Each
`N_n ⊇ <<R>>` is a normal subgroup of `Λ` with simple quotient, so

```text
E[X(Λ)] >= Σ_(n odd, n >= 5) P[R ⊆ N_n] >= Σ_(n odd, n >= 5) p_0 = ∞.
```

Any member with `R ⊆ T_0` surjects onto `F_m/<<a³>> = Z/3 * F_(m−1)`, whose
abelianization contains `Z^(m−1)`. Property (T) forces finite abelianization, so
these members are not Kazhdan.

## Exact checks (MSI, 2026-09-13)

`experiments/hyperbolic-rf/density_quotient_checks.py` verified:
- `⟨(1 2 3), σ⟩ = A_n` for `n = 5, 7, 9`, by closure;
- for `(m, r) = (2, 2), (2, 3), (3, 2)`, the words `W` are distinct and cyclically
  reduced of length `6r+9`, and their number meets the lower bound of Step 1.
