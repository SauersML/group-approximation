---
rg: 2
id: thompson-f-near-eigenvectors-need-log-scale-pointer-spread-proof
kind: route
title: Split the Rayleigh value into the pointer-right and merge correlations, turn each into a one-sided total-variation bound on the pushed-forward size law, and cover min(s,r) <= 2^J by J+1 dyadic crossings
target: thompson-f-near-eigenvectors-need-log-scale-pointer-spread
requires:
  - thompson-f-one-sided-forest-windows-are-norm-lossless
  - thompson-f-norm-bound-from-forest-renewal-test-vector
artifacts:
  - experiments/thompson-f-log-scale-spread-2026-09-17/spread_check.py
  - experiments/thompson-f-log-scale-spread-2026-09-17/spread_check_n9.out
---

**Imports.** Only two ESTABLISHED nodes are used, cited by item.
- *Cayley edges.* `thompson-f-norm-bound-from-forest-renewal-test-vector-proof`, step 2: pointer right is
  the Cayley edge of `s_0` and merge is the Cayley edge of `s_1`, and pointer left and split are the
  inverse moves. Fix the side on which `F` acts in that step, and write `x·g` for the neighbour of `x`
  along `g`. Then `right(x) = x·s_0` and `merge(x) = x·s_1` as elements of `F`.
- *One-sided model.* `thompson-f-one-sided-forest-windows-are-norm-lossless`, item 3: `R` is the set of
  one-sided pointed forests, and pointer right and merge are defined at every vertex of `R` and land
  in `R`. From the moves themselves:
  - `right(T_0, T_1, ...; i) = (T_0, T_1, ...; i + 1)`;
  - `merge` replaces `T_i, T_{i+1}` by the tree `(T_i, T_{i+1})` and keeps the pointer at `i`.
  - So `s(right x) = r(x)` and `s(merge x) = s(x) + r(x)`.

**Step 1 (the Rayleigh value is two correlations).** For `g ∈ F` let `ρ(g)f(x) = f(x·g)`. This is a
unitary of `l^2(F)` with `ρ(g^{-1}) = ρ(g)^*`, and `K` acts as `Σ_g ρ(g)` over the four generators.
So `<f, ρ(g^{-1}) f> = <ρ(g) f, f> = <f, ρ(g) f>`, since `f` is real. Hence
`<f, K f> = 2 a_0 + 2 a_1` with `a_0 = <f, ρ(s_0) f>` and `a_1 = <f, ρ(s_1) f>`.

Each `a_j ≤ ||f|| ||ρ(s_j) f|| = 1`, so `<f, K f> ≥ 4 − δ` gives `a_0, a_1 ≥ 1 − δ/2`. Put
`h_j = ρ(s_j) f`. Then `||f − h_j||^2 = 2 − 2 a_j ≤ δ`.

**Step 2 (one-sided transport).** Let `A ⊆ R`. Then `h_j^2(A) = Σ_{x∈A} f(x·s_j)^2 = μ(A·s_j)`, and

`μ(A) − μ(A·s_j) ≤ Σ_x |f(x)^2 − h_j(x)^2| ≤ ||f − h_j|| ||f + h_j|| ≤ 2√δ`,

by Cauchy–Schwarz, with `||f + h_j|| ≤ 2`.

**Step 3 (item 1).** Take `A = {x ∈ R : s(x) + r(x) > t}` and `j = 1`. Then
`A·s_1 = merge(A) ⊆ {y ∈ R : s(y) > t}`, because `s(merge x) = s(x) + r(x)`. By Step 2,
`μ(s + r > t) ≤ μ(s > t) + 2√δ`.

Since `r ≥ 1 > 0`, `{s + r ≤ t} ⊆ {s ≤ t}`. So
`μ(s ≤ t < s + r) = μ(s ≤ t) − μ(s + r ≤ t) = μ(s + r > t) − μ(s > t) ≤ 2√δ`. ∎

**Step 4 (item 2).** Take `A = {x ∈ R : r(x) ≤ t}` and `j = 0`. Then
`A·s_0 = right(A) ⊆ {y : s(y) ≤ t}`, because `s(right x) = r(x)`. By Step 2,
`μ(r ≤ t) ≤ μ(s ≤ t) + 2√δ`.

Since `s ≥ 1`, `{r ≤ t} ⊇ {r + s ≤ t}`. So
`μ(r ≤ t < r + s) = μ(r ≤ t) − μ(s + r ≤ t) ≤ [μ(s ≤ t) − μ(s + r ≤ t)] + 2√δ ≤ 4√δ`, by item 1. ∎

**Step 5 (item 3).** Let `min(s, r) ≤ 2^J` at `x`.
- Suppose `s ≤ r`. Let `j = ⌈log_2 s⌉ ∈ {0, ..., J}`. Then `s ≤ 2^j < 2s ≤ s + r`: if `s ≥ 2` then
  `2^{j−1} < s`, and if `s = 1` then `2^0 = 1 < 2`. So `x ∈ {s ≤ 2^j < s + r}`.
- Suppose `r < s`. The same with `s` and `r` exchanged gives `x ∈ {r ≤ 2^j < r + s}`.

Items 1 and 2, summed over `j = 0..J`, give `μ(min(s, r) ≤ 2^J) ≤ (J + 1)(2√δ + 4√δ)`. ∎

The two consequences recorded in the theorem:
- `{s ≤ t < r} ⊆ {s ≤ t < s + r}`;
- `{r ≤ t < s} ⊆ {r ≤ t < r + s}`.

**Step 6 (corollaries).**
- *C1.* Put `J = ⌈log_2 N⌉`. Then `{s ≤ N} ⊆ {min(s, r) ≤ 2^J}`, so `c ≤ 6(J + 1)√δ`, and squaring
  gives the bound on `δ`.
  - For a signed `f` with the same support, `<|f|, K|f|> ≥ <f, K f>`, because `K` has nonnegative
    entries.
  - `||K|| = 4||P||` converts `4 − ε` into `1 − ε/4`.
- *C2.* This is item 3 with `J = J_δ`, since `6(J_δ + 1)√δ ≤ 1/2`.
  - The Kesten equivalence is item 2 of the lossless node.
  - `min(s, r) → ∞` in probability also follows from item 3: for each fixed `J`, the bound tends to
    `0` as `δ → 0`.
  - The one-sided closeness of the laws of `s`, `s + r` and `r` is exactly Steps 3–4. ∎

**Checks** (`spread_check.py`, float, output in `spread_check_n9.out`). They run on the Perron vector and
on a random nonnegative vector of the move graph on `S_n`, for `n = 2..9`, viewed on `R` (states with
`i = m − 1` have neighbour a leaf, so `r = 1`):
- the identity `<f, A_n f> = 2 a_0 + 2 a_1`;
- `||f − h_j||^2 ≤ δ`;
- the Step 2 inequality at every threshold;
- item 3 for `J = 0..4`.

At these `n`, `δ ≥ 0.88`, so item 3 is vacuous there. The script checks the chain of inequalities, not
their strength.

**Trust surface.**
- Two ESTABLISHED imports: the Cayley-edge dictionary and the fact that right and merge are total on
  `R`.
- Otherwise only Cauchy–Schwarz and set inclusions. No computation enters the proof.
- Not reviewed by a second agent.
