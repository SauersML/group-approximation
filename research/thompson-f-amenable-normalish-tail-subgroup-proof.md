---
rg: 2
id: thompson-f-amenable-normalish-tail-subgroup-proof
kind: route
title: Conjugating an x_0-translated bump sequence by an element with germ 2^k at 0 shifts the index by k
target: thompson-f-has-an-amenable-normalish-tail-subgroup
requires: []
---

`F` acts on `[0,1]` by PL homeomorphisms with dyadic breakpoints and slopes in `2^Z`. `x_0(t) = t/2`
on `[0,1/2]`, `x_0(t) = t - 1/4` on `[1/2,3/4]`, `x_0(t) = 2t - 1` on `[3/4,1]`. `x_1` is the identity
on `[0,1/2]`. Nontrivial elements supported in `[1/4,1/2]` exist, since that subgroup is a copy of `F`.

**Step 1 (formula for h_n).** For `s ∈ [0, 2^(-n-1)]` we have `x_0^(-n)(s) = 2^n s`. By induction: if
`s ≤ 2^(-j-1)` then `s ≤ 1/4`, so `x_0^(-1)(s) = 2s ≤ 2^(-j)`. For `u ∈ [0,1/2]`, `x_0^n(u) = 2^(-n) u`.
Hence `h_n = x_0^n h_0 x_0^(-n)` equals `s ↦ 2^(-n) h_0(2^n s)` on `[0, 2^(-n-1)]`. It is the identity
outside `x_0^n([1/4,1/2]) = [2^(-n-2), 2^(-n-1)]`.

The open supports are pairwise disjoint, so the `h_n` commute. Each `h_n ≠ 1` has infinite order,
because `F` is torsion-free. A relation `∏ h_n^(a_n) = 1` restricted to the `n`-th support gives
`h_n^(a_n) = 1`, so `a_n = 0`. Hence `T ≅ ⊕_(n≥0) Z`, which is abelian and therefore amenable.

**Step 2 (germ rule).** Every `g ∈ F` fixes `0` and has finitely many breakpoints, so `g(t) = 2^k t`
on some `[0,ε]`. Let `n ≥ N(g) = max(k, ⌈log_2(1/ε)⌉)`. Then `supp h_n ⊆ [0, 2^(-n-1)] ⊆ [0,ε]`, and on
`g(supp h_n) = [2^(k-n-2), 2^(k-n-1)]` we have `g^(-1)(s) = 2^(-k) s`. Since `h_n` preserves its support,
for `s` in that interval:

`g h_n g^(-1)(s) = 2^k · 2^(-n) h_0(2^n · 2^(-k) s) = 2^(-(n-k)) h_0(2^(n-k) s) = h_(n-k)(s)`.

This uses `n - k ≥ 0` and Step 1 for the index `n - k`. Outside that interval both sides are the
identity, since `supp h_(n-k) = [2^(k-n-2), 2^(k-n-1)]`. So `g h_n g^(-1) = h_(n-k)`.

**Step 3 (tails).** By Step 2, `h_m = g h_(m+k) g^(-1) ∈ g T g^(-1)` for every `m ≥ max(0, N(g) - k)`.
Given `g_1, …, g_r` with germ exponents `k_i`, put `M = max_i max(0, N(g_i) - k_i)`. Then
`T_(≥M) ⊆ ⋂_i g_i T g_i^(-1)`, and `T_(≥M)` is infinite. So `T` is normalish.

**Step 4.** `x_0^(-1) h_(n+1) x_0 = h_n`, so `T ⊆ x_0^(-1) T x_0`. The generator `x_1` is the identity on
`[0,1/2] ⊇ supp h_n`, so it commutes with every `h_n`, and `x_1^(-1) T x_1 = T`.

**Non-commensuration.** `x_0 T x_0^(-1) = T_(≥1)`, and `T / T_(≥1) ≅ Z` is infinite. ∎
