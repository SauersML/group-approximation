---
rg: 2
id: monotone-injective-chain-automata-are-translations-proof
kind: route
title: Induction on the chain length, splitting a finite defect at level one and closing with charge noncreation
target: monotone-injective-chain-automata-are-translations
requires:
  - monotone-binary-injective-rules-are-copies
  - finite-injective-charge-noncreation-forces-surjectivity
artifacts:
  - experiments/monotone-poset-ascent-2026-09-17/chain_search_results.txt
---

Complete proof. Automata act by `ρ(x)(h) = μ((x(hm))_{m ∈ M})`, so `ρ(x)(h)` depends only on `x|_{hM}`. Write
`[a,b]` for the subchain `{a, ..., b}` of `L = [0, k-1]`, and order configurations sitewise. Say `ρ` is a *copy of
`t`* if `ρ(x)(h) = x(ht)` for all `x, h`. Statement `T(k)`: every monotone injective automaton on `[0,k-1]^G`, over
any group, is a copy of some `t`. Induct on `k`.

## Step 0. Constants and invariant subchains

`ρ` sends constants to `G`-invariant configurations, which are constants. It is injective, so it permutes the `k`
constants, and monotone, so the permutation preserves the order of a chain. So it is the identity: `ρ(c^G) = c^G`.
For `a <= b`, if `a^G <= x <= b^G` then `a^G = ρ(a^G) <= ρ(x) <= ρ(b^G) = b^G`. So `[a,b]^G` is `ρ`-invariant, and
`ρ` restricted to it is a monotone injective automaton on a chain of `b - a + 1` letters (same memory, rule
restricted).

## Step 1. Base cases

`T(1)` is trivial (take `t = 1`). `T(2)` is `monotone-binary-injective-rules-are-copies`: the rule is `μ = x_t`
for one address `t ∈ M`, which says `ρ(x)(h) = x(ht)`.

## Step 2. Splitting a finite defect at level one (k >= 3)

Assume `T(2)` and `T(k-1)`. By Step 0, `ρ` restricted to `[0,1]^G` is a copy of some `t`, and `ρ` restricted to
`[1,k-1]^G` is a copy of some `t'` (relabel `[1,k-1]` as `[0,k-2]`).

Call `x` *finite* if `S(x) = {g : x(g) != 1}` is finite. Put `x_- = min(x, 1^G)` and `x_+ = max(x, 1^G)`,
sitewise. Then `x_- ∈ [0,1]^G`, `x_+ ∈ [1,k-1]^G`, `x_- <= x <= x_+`, and
`S(x) = S(x_-) ⊔ S(x_+)`, where `S(x_-) = x^{-1}(0)` and `S(x_+) = x^{-1}([2,k-1])`. Monotonicity gives

    x_-(ht) = ρ(x_-)(h) <= ρ(x)(h) <= ρ(x_+)(h) = x_+(ht').

If `ht ∉ S(x_-)` and `ht' ∉ S(x_+)`, both bounds equal `1`, so `ρ(x)(h) = 1`. Hence

    S(ρ(x)) ⊆ S(x_-) t^{-1} ∪ S(x_+) t'^{-1},   so   |S(ρ(x))| <= |S(x)|.      (1)

## Step 3. Charge noncreation

Give the letter `1` charge `0` and every other letter charge `1`. Then `W(x) = |S(x)|`. By Step 0 `ρ` fixes `1^G`.
It is injective, so injective on finite configurations. By (1), `W(ρ(x)) <= W(x)` for every finite `x`. By
`finite-injective-charge-noncreation-forces-surjectivity` (distinguished symbol `1`, all other charges positive):

    |S(ρ(x))| = |S(x)|   for every finite x.                                   (2)

## Step 4. The two translations agree

Suppose `t != t'`. Pick any `p ∈ G` and put `q = p t^{-1} t'`, so `q != p` and `q t'^{-1} = p t^{-1}`. Let `x`
be `0` at `p`, `2` at `q` (a letter of `[1,k-1]` other than `1`, since `k >= 3`), and `1` elsewhere. Then
`S(x_-) = {p}`, `S(x_+) = {q}` and `|S(x)| = 2`. By (1), `S(ρ(x)) ⊆ {p t^{-1}}`, so `|S(ρ(x))| <= 1`, against (2).
So `t = t'`.

## Step 5. Exact values

With `t = t'`, (1) and (2) give `S(ρ(x)) = S(x) t^{-1}` for finite `x`, because the right side of (1) has exactly
`|S(x)|` elements. Fix `x` and `h`, and put `g = ht`, `c = x(g)`.
- If `1 <= c <= k-2`: put `x_lo = min(x, (k-2)^G) ∈ [0,k-2]^G` and `x_hi = max(x, 1^G) ∈ [1,k-1]^G`. By `T(k-1)`
  on both subchains, `ρ` restricted to `[0,k-2]^G` is a copy of some `t''`. It agrees with `t` on `[0,1]^G`, since
  `k-2 >= 1`. A copy of `t''` restricted to `{0,1}^G` is a copy of `t''`, and copies of distinct elements differ
  on `{0,1}^G`, so `t'' = t`. Then `min(c, k-2) <= ρ(x)(h) <= max(c, 1)`, which is `c`.
  Note `t ∈ M`, since `T(2)` gives `μ|_{{0,1}^M} = x_t` for an address `t`; so `g = ht ∈ hM`.
- If `c = 0`: `ρ(x)(h)` depends only on `x|_{hM}`. Let `x'` agree with `x` on `hM` and be `1` elsewhere. Then
  `x'` is finite, `ρ(x')(h) = ρ(x)(h)` and `x'(g) = 0`. Since `h ∈ S(x') t^{-1} = S(ρ(x'))`, we get
  `ρ(x')(h) != 1`. Also `ρ(x')(h) <= x'_+(ht) = 1`. So `ρ(x)(h) = 0`.
- If `c = k-1`: the mirror argument. Repeat Steps 2–4 at level `k-2`, splitting into `[0,k-2]` (a copy of `t`, by the
  first case) and `[k-2,k-1]` (a copy of some `t'''`, by `T(2)`). Step 4 uses the letters `0` and `k-1`, and gives
  `t''' = t`. Then `S_{k-2}(ρ(y)) = S_{k-2}(y) t^{-1}` for every `y` with finitely many sites outside `k-2`. Let `x'`
  agree with `x` on `hM` and be `k-2` elsewhere. Then `ρ(x')(h) = ρ(x)(h)` and `ρ(x')(h) != k-2`. Also
  `ρ(x')(h) >= min(x', (k-2)^G)(ht) = k-2`. So `ρ(x)(h) = k-1`.

So `ρ(x)(h) = x(ht)` in every case. This proves `T(k)`.

## Remarks

- For `k = 3` the first case of Step 5 is empty and `[0,k-2] = [0,1]`, so only `T(2)` is used.
- Only the chain structure is used in Step 0 (a monotone permutation of a chain is the identity) and in Step 2 (the
  sitewise `min` and `max` with a constant exist and bracket `x`). The same splitting works in any finite poset at a
  level `c` that is comparable with every letter. See `monotone-strict-automata-ascend-along-poset-homs` for what
  survives in general posets.
- Step 5, case `c = 0`, uses that `S(x') t^{-1}` contains `h`, since `x'(ht) = 0`, and (2) with the equality
  `S(ρ(x')) = S(x') t^{-1}`.
