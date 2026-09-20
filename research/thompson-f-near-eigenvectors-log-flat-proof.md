---
rg: 2
id: thompson-f-near-eigenvectors-log-flat-proof
kind: route
title: Move the one-scale merge and pointer-right bounds to offset j by j pointer-right transports, integrate them against dt/t up to a truncation T, and combine the window bound with Moore's two-slot tower by Markov's inequality
target: thompson-f-near-eigenvectors-are-log-flat-near-the-pointer
requires:
  - thompson-f-near-eigenvectors-need-log-scale-pointer-spread
  - thompson-f-near-eigenvectors-carry-a-root-local-moore-tower
  - thompson-f-one-sided-forest-windows-are-norm-lossless
artifacts:
  - experiments/thompson-f-log-flat-window-2026-09-17/log_flat_check.py
  - experiments/thompson-f-log-flat-window-2026-09-17/log_flat_check_n9.out
---

Notation is that of the target. `f ≥ 0` is a unit vector of `l^2(F)` with `supp f ⊆ R`, `μ = f^2`,
`δ = 4 − <f, K f>`, `η = δ/4`, `s_j = |T_{i+j}|` and `L_j = ln min(s_j, T)`.

## Imports (verbatim)

**(I1)** `thompson-f-one-sided-forest-windows-are-norm-lossless`, item 3:
> `R = ∪_n E(S_n)` is the set of pointed forests `(T_0, T_1, ...; i)` on the roots `0, 1, 2, ...`,
> with finitely many nontrivial trees and pointer `i >= 0`. It is the image of the positive monoid of
> `F`. The compression of `K` to `l^2(R)` has norm exactly `||K||`. Its graph `Gamma_R` has pointer
> right and merge at every vertex, pointer left iff `i > 0`, and split iff the pointer tree `T_i` is
> not a leaf.

**(I2)** `thompson-f-near-eigenvectors-need-log-scale-pointer-spread-proof`, Step 2 (with Step 1's
`h_j = ρ(s_j) f` and `||f − h_j||^2 ≤ δ`), which is the proof of items 1–2 of the spread claim:
> Let `A ⊆ R`. Then `h_j^2(A) = Σ_{x∈A} f(x·s_j)^2 = μ(A·s_j)`, and
> `μ(A) − μ(A·s_j) ≤ Σ_x |f(x)^2 − h_j(x)^2| ≤ ||f − h_j|| ||f + h_j|| ≤ 2√δ`,
> by Cauchy–Schwarz, with `||f + h_j|| ≤ 2`.

and from the import list of that route, `right(x) = x·s_0`, `merge(x) = x·s_1`, with
> `right(T_0, T_1, ...; i) = (T_0, T_1, ...; i + 1)`;
> `merge` replaces `T_i, T_{i+1}` by the tree `(T_i, T_{i+1})` and keeps the pointer at `i`.

**(I3)** `thompson-f-near-eigenvectors-need-log-scale-pointer-spread`, Theorem, items 1–2:
> 1. **(Merge at one scale.)** `μ(s ≤ t < s + r) ≤ 2√δ` for every real `t`.
> 2. **(Pointer right at one scale.)** `μ(r ≤ t) ≤ μ(s ≤ t) + 2√δ`, and hence `μ(r ≤ t < r + s) ≤ 4√δ`.

**(I4)** `thompson-f-near-eigenvectors-carry-a-root-local-moore-tower`, Corollary B:
> Let `f ≥ 0` be a unit vector on `R` with `η = η(f)`. Let `n ≥ 0` satisfy `12 K_0^(n+1) √η ≤ 1`.
> Then `f²({v : |T_i| < 2 exp_(n+4)(0) and |T_(i+15)| < 2 exp_(n+4)(0)}) ≤ 24 K_0^(n+2) √η`.

There `η(f) = 1 − ⟨f, K f⟩/4`, which is `δ/4` here, so `√δ = 2√η`.

## Step 1 (pointer-right transport over `j` places)

**Lemma 1.** For every `B ⊆ R` and `j ≥ 0`, `μ(right^{-j}(B)) ≤ μ(B) + 2j√δ`.

*Proof.* By (I1), `right` is defined on all of `R` and lands in `R`, so `A_m = right^m(A)` is a subset
of `R` for every `A ⊆ R` and `m ≥ 0`. By (I2) with the generator `s_0`, `A_m·s_0 = right(A_m) = A_{m+1}`
and `μ(A_m) − μ(A_{m+1}) ≤ 2√δ`. Summing over `m < j` gives `μ(A) − μ(right^j(A)) ≤ 2j√δ`.
Take `A = right^{-j}(B) = {x ∈ R : right^j(x) ∈ B}`. Then `right^j(A) ⊆ B`, so
`μ(A) ≤ μ(right^j(A)) + 2j√δ ≤ μ(B) + 2j√δ`. ∎

**Offsets.** By (I2), `right^j(T_0, T_1, ...; i) = (T_0, T_1, ...; i + j)`. So
`s(right^j x) = s_j(x)` and `r(right^j x) = s_{j+1}(x)`, where `s = s_0` and `r = s_1` are the
functions of the spread claim.

## Step 2 (Theorem 1, item 1)

Fix a real `t`. Let `E(t) = {y ∈ R : s(y) ≤ t < s(y) + r(y)}` and
`E'(t) = {y ∈ R : r(y) ≤ t < r(y) + s(y)}`. By the offset identity,

`{x : s_j ≤ t < s_j + s_{j+1}} = right^{-j}(E(t))` and
`{x : s_{j+1} ≤ t < s_j + s_{j+1}} = right^{-j}(E'(t))`.

By (I3), `μ(E(t)) ≤ 2√δ` and `μ(E'(t)) ≤ 4√δ`. Lemma 1 gives the bounds `(2 + 2j)√δ` and
`(4 + 2j)√δ`. ∎

## Step 3 (Fubini)

**Lemma 2.** For integers (or reals) `a, b ≥ 1` and real `T > 1`,

`ln min(a + b, T) − ln min(a, T) = ∫_1^T 1[a ≤ t < a + b] dt/t`.

*Proof.* Both sides vanish if `a ≥ T`. If `a < T`, the left side is `∫_a^{min(a+b,T)} dt/t`, and for
`t ∈ [1, T)` the condition `a ≤ t < a + b` is `a ≤ t < min(a + b, T)`. ∎

Apply Lemma 2 with `(a, b) = (s_j, s_{j+1})` and with `(a, b) = (s_{j+1}, s_j)`. The integrands are
nonnegative and jointly measurable (`R` is countable), so Tonelli and Step 2 give

`E_μ[ln min(s_j + s_{j+1}, T) − L_j] = ∫_1^T μ(s_j ≤ t < s_j + s_{j+1}) dt/t ≤ (2 + 2j)√δ ln T`,

`E_μ[ln min(s_j + s_{j+1}, T) − L_{j+1}] ≤ (4 + 2j)√δ ln T`.

## Step 4 (Theorem 1, items 2 and 3)

For `a, b ≥ 1` put `M = ln min(a + b, T)`, `A = ln min(a, T)` and `B = ln min(b, T)`. Then
`M ≥ max(A, B)`, because `min(·, T)` is nondecreasing. Hence

`|A − B| = max(A, B) − min(A, B) ≤ M − min(A, B) ≤ (M − A) + (M − B)`,

with both brackets nonnegative. Taking `(a, b) = (s_j, s_{j+1})` and adding the two bounds of Step 3,

`E_μ |L_j − L_{j+1}| ≤ (6 + 4j)√δ ln T`.

This is item 2. For item 3 sum over `j < W`:
`Σ_{j<W} (6 + 4j) = 6W + 2W(W − 1) = 2W(W + 2)`. ∎

## Step 5 (Corollary 2)

Item 2 with `j = 0` gives `γ_T(f) ≤ 6√δ` for every `T > 1`, so `δ ≥ (γ*/6)^2` and
`<f, K f>/4 = 1 − δ/4 ≤ 1 − γ*^2/144`. For signed `f`, `|f|` has the same `μ` and
`<|f|, K|f|> ≥ <f, K f>` because `K` has nonnegative entries.

*Scale-limit form.* Fix `C > 0` and put `T_k = e^{C λ_k} > 1`. Then
`L_0/ln T_k = min(ln s/λ_k, C)/C`, and the same for `L_1` with `r`. The map
`(y, y') ↦ |y ∧ C − y' ∧ C|/C` is bounded and continuous on `[0, ∞]^2`, so convergence in law gives
`γ_{T_k}(f_k) → E|Y ∧ C − Y' ∧ C|/C`, and `δ(f_k) ≥ (γ_{T_k}(f_k)/6)^2` gives the liminf bound.
For offset `j` use item 2 with `6 + 4j`.

*Positivity.* If `P(Y ≠ Y') > 0` then, since `Y ≠ Y'` forces `min(Y, Y') < ∞`, there is `C` with
`P(Y ≠ Y', min(Y, Y') < C) > 0`, and on that event `Y ∧ C ≠ Y' ∧ C`. Conversely `Y = Y'` a.s. makes
every term vanish. ∎

*Example.* For `Y, Y'` i.i.d. uniform on `[0, 1]` and `C = 1`, `E|Y − Y'| = 1/3`, so
`liminf δ ≥ 1/324` and `limsup <f_k, K f_k>/4 ≤ 1 − 1/1296`.

## Step 6 (Corollary 3)

Let `E_n = 2 exp_{n+4}(0)`, `T = E_n`, and `W ≥ 15`. Let `G` be the complement of the set in (I4),
so `μ(R ∖ G) ≤ 24 K_0^{n+2} √η`, and on `G` we have `max(s_0, s_15) ≥ T`, i.e.
`L_0 = ln T` or `L_15 = ln T`.

Let `x ∈ G` have `s_j(x) < T^{1/2}` for some `j ≤ W`, so `L_j < (1/2) ln T`. Let `k ∈ {0, 15}` have
`L_k = ln T`. Both `j` and `k` lie in `{0, ..., W}`, so by the triangle inequality along the path
between them, `Σ_{m<W} |L_{m+1} − L_m| ≥ L_k − L_j > (1/2) ln T`. By Markov's inequality and item 3,

`μ(G ∩ {∃ j ≤ W : s_j < T^{1/2}}) ≤ 2 · 2W(W + 2)√δ = 8W(W + 2)√η`.

Adding `μ(R ∖ G)` gives the bound. Finally `T^{1/2} ≥ exp_{n+4}(0)^{1/2} = 2^{exp_{n+3}(0)/2}`, and
`2^{x/2} ≥ x` for `x ≥ 4`. Since `n ≥ 0`, `exp_{n+3}(0) ≥ exp_3(0) = 4`. So `T^{1/2} ≥ exp_{n+3}(0)`. ∎

*Numbers.* With `n = ⌊log_{K_0}(1/(96√η))⌋ − 2 ≥ 0`, `K_0^{n+2} ≤ 1/(96√η)`, so
`24 K_0^{n+2} √η ≤ 1/4`, and `12 K_0^{n+1} √η ≤ 1/(8 K_0) ≤ 1`. With `W + 1 ≤ η^{-1/4}/8`,
`8W(W + 2)√η < 8(W + 1)^2 √η ≤ 1/8`. The total bad mass is at most `3/8`.

## Step 7 (Corollary 4)

Suppose `μ`-a.e. `s_{j_0} < N`, and put `W = max(15, j_0)` and `n = max(log* N − 3, 0)`. Then
`n + 3 ≥ log* N`, so `exp_{n+3}(0) ≥ N`, and every `x` lies in the bad set of Corollary 3 (with
`j = j_0 ≤ W`). Two cases.
- If `12 K_0^{n+1} √η > 1`, then `η > K_0^{−2n−2}/144`.
- Otherwise Corollary 3 applies and `1 ≤ (24 K_0^{n+2} + 8W(W + 2))√η ≤ (24 + 8W(W + 2)) K_0^{n+2} √η`,
  using `K_0 ≥ 1`. So `η ≥ (24 + 8W(W + 2))^{-2} K_0^{−2n−4}`.

Both lower bounds are at least `(24 + 8W(W + 2))^{-2} K_0^{−2n−4}`, and `n ≤ log* N` gives the claim.
For `W = 15`, `24 + 8·15·17 = 2064`. ∎

## Trust surface

- Imports: (I1)–(I4), all ESTABLISHED lane results, quoted above. (I4) carries the Moore machinery and
  the uncomputed constant `K_0`. Theorem 1 and Corollary 2 do not use (I4).
- New steps: Lemma 1 (iteration of one inequality), Lemma 2 (an integral identity), Tonelli, one
  elementary inequality between logarithms, and Markov's inequality.
- No computation enters the proof. `log_flat_check.py` checks items 1–3 and the Fubini identity on
  small windows in floating point, where `δ` is large.
- Not reviewed by a second agent.
