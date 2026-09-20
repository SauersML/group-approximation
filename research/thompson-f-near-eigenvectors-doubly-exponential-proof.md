---
rg: 2
id: thompson-f-near-eigenvectors-doubly-exponential-proof
kind: route
title: Hellinger control of the two moves, additive and multiplicative merge test events with favourable perturbations, and a tent lemma for positive reals applied to log size ratios
target: thompson-f-near-eigenvectors-need-doubly-exponential-tree-sizes
requires: []
artifacts:
  - experiments/thompson-f-doubly-exponential-profile-2026-09-17/loglevel_check.py
  - experiments/thompson-f-doubly-exponential-profile-2026-09-17/loglevel_check.out
---

**Conventions.** These are those of `thompson-f-one-sided-forest-windows-are-norm-lossless`, items 1, 3 and 4.
- `R` is the set of one-sided pointed forests `v = (T_0, T_1, ...; i)`.
- `ρ(v) = (T_0, T_1, ...; i+1)`. It is a bijection `R -> {i >= 1}`.
- `μ(v)` replaces `T_i, T_(i+1)` by the single tree `(T_i, T_(i+1))` and shifts `T_(i+2), ...` one place left. It
  is a bijection `R -> {T_i not a leaf}`.
- Every edge of the compressed Cayley graph `Γ_R` is `{v, ρv}` or `{v, μv}`. By item 3 there, for `f >= 0`,
  `⟨f, K f⟩ = 2 Σ_v f(v) f(ρv) + 2 Σ_v f(v) f(μv)`.
- `sup ⟨f, K f⟩ = ||K|| = 4||P||` over unit `f >= 0` on `R`. Put `⟨f, P f⟩ := ⟨f, K f⟩/4` and
  `η = 1 − ⟨f, P f⟩`.
- `Q = f²`. `n_j(v)` is the number of leaves of `T_(i+j)`, defined for `j >= −i`.
- All events below are defined by finitely many of the `n_j` together with a pointer condition that makes those
  `n_j` defined.

## Step 1. Hellinger control of the two moves

For `g ∈ {ρ, μ}`, `g` is injective, so `g_*Q(gv) = Q(v)`. Hence
`BC_g := Σ_w sqrt(Q(w) g_*Q(w)) = Σ_v f(v) f(gv)`, and `⟨f, P f⟩ = (BC_ρ + BC_μ)/2`.

Let `t_g = TV(Q, g_*Q)`. The inequality `TV <= sqrt(1 − BC²) <= sqrt(2(1 − BC))` and Cauchy–Schwarz give
`t_ρ + t_μ <= √2 (sqrt(1 − BC_ρ) + sqrt(1 − BC_μ)) <= 2 sqrt((1 − BC_ρ) + (1 − BC_μ)) = 2√2 √η`.

For every event `E` and each `g`: `|Q(g^(-1) E) − Q(E)| = |g_*Q(E) − Q(E)| <= t_g`.

**Two consequences used repeatedly.**
- (T1) If `E ⊆ μ^(-1) E`, then `Q(μ^(-1) E ∖ E) = Q(μ^(-1) E) − Q(E) <= t_μ`.
- (T2) For any `E`, `Q(μ^(-1) E ∖ ρ^(-1) E) = Q(μ^(-1) E) − Q(ρ^(-1) E) + Q(ρ^(-1) E ∖ μ^(-1) E)`, which is at most
  `t_μ + t_ρ + Q(ρ^(-1) E ∖ μ^(-1) E)`.
- (T1') Similarly, `Q(μ^(-1) E ∖ E) <= t_μ + Q(E ∖ μ^(-1) E)` for any `E`.

## Step 2. Pull-backs of the size coordinates

Directly from the definitions:
- `n_j(ρv) = n_(j+1)(v)`, and `ρv` has pointer `i + 1`;
- `n_0(μv) = n_0 + n_1`;
- `n_j(μv) = n_(j+1)` for `j >= 1`;
- `n_j(μv) = n_j` for `−i <= j <= −1`, and `μv` has pointer `i`.

So `v ∈ μ^(-1) E` iff the defining inequalities of `E` hold after the substitution
`(n_(−2), n_(−1), n_0, n_1, n_2, ...) -> (n_(−2), n_(−1), n_0 + n_1, n_2, n_3, ...)`, with the same pointer.
Likewise `v ∈ ρ^(-1) E` iff they hold after `n_j -> n_(j+1)` with pointer `i + 1`.

**Shift rule.** Let `X_k` be defined by a pointer condition `i + k − c >= 0` and a condition on
`n_(k−c), ..., n_(k+d)` that does not depend on `k`. Then `ρ^(-1) X_k = X_(k+1)`. Hence
`|Q(X_(k+1)) − Q(X_k)| <= t_ρ`, and `Q(X_k) <= Q(X_(k0)) + |k − k0| t_ρ`.

## Step 3. Level-0 merge tests (the wave-17 bound, reproved)

For `j >= 1 − i`, write `(a, b, c) = (n_(j−1), n_j, n_(j+1))`. Let `C1_j = {b <= c < a + b}`,
`C2_j = {b <= a < b + c}`, and `bad_j = {i + j <= 0} ∪ C1_j ∪ C2_j`.

- `ρ_*Q` is supported on `{i >= 1}`, so `Q(i = 0) <= t_ρ`.
- Take `E = {i >= 1, n_(−1) < n_0}`. Then `μ^(-1) E = {i >= 1, n_(−1) < n_0 + n_1} ⊇ E`, and the difference is
  `C2_0 ∩ {i >= 1}`. By (T1), `Q(C2_0 ∩ {i >= 1}) <= t_μ`.
- Take `E = {n_0 > n_1}`. Then `ρ^(-1) E = {n_1 > n_2} ⊆ μ^(-1) E = {n_0 + n_1 > n_2}`, and the difference is `C1_1`.
  By (T2), `Q(C1_1) <= t_μ + t_ρ`. By the shift rule, `Q(C1_0 ∩ {i >= 1}) <= t_μ + 2 t_ρ`.
- Summing, `Q(bad_0) <= 2 t_μ + 3 t_ρ`. `bad_j` obeys the shift rule, so `Q(bad_j) <= Q(bad_0) + |j| t_ρ`.

**Local step (positive reals).** Let `a, b, c > 0` be real, with `(a, b, c) ∉ C1 ∪ C2`.
- If `b <= c`, then `c >= a + b` (not C1). If moreover `a >= b`, then not C2 gives `a >= b + c > c >= a + b > a`,
  a contradiction. So `a < b`.
- Mirror: if `b <= a`, then `a >= b + c` and `c < b`.
- In particular, a weak local minimum `b <= min(a, c)` lies in `C1 ∪ C2`.

## Step 4. Level-1 (multiplicative) merge tests

**Definitions.** Put `y_j = log(n_(j+1)/n_j)` and `z_j = −y_j = log(n_j/n_(j+1))`.
- `A^inc_k = {i + k − 1 >= 0, n_(k−1) < n_k < n_(k+1) < n_(k+2)}`. `A^dec_k` is the same with `>`.
- `C1inc_k = A^inc_k ∩ {y_k <= y_(k+1) < y_(k−1) + y_k}`.
- `C2inc_k = A^inc_k ∩ {y_k <= y_(k−1) < y_k + y_(k+1)}`.
- `C1dec_k = A^dec_k ∩ {z_k <= z_(k+1) < z_(k−1) + z_k}`.
- `C2dec_k = A^dec_k ∩ {z_k <= z_(k−1) < z_k + z_(k+1)}`.

On `A^inc_k` the `y`-triple is positive, and on `A^dec_k` the `z`-triple is positive. All four families obey the
shift rule.

Written multiplicatively, with `(a, b, c, d) = (n_(k−1), n_k, n_(k+1), n_(k+2))`:
- `C1inc_k = A^inc_k ∩ {c² <= b d, a d < c²}`;
- `C2inc_k = A^inc_k ∩ {a c <= b², b² < a d}`;
- `C1dec_k = A^dec_k ∩ {b d <= c², c² < a d}`;
- `C2dec_k = A^dec_k ∩ {b² <= a c, a d < b²}`.
Note that `y_(k−1) + y_k = log(c/a)`, and similarly for `z`.

**(4a) `Q(C2inc_(−1)) <= t_μ`.** Take `E = {i >= 2, n_(−1)² < n_(−2) n_0}`, that is `{y_(−2) < y_(−1)}`.
- By Step 2, `μ^(-1) E = {i >= 2, n_(−1)² < n_(−2)(n_0 + n_1)} ⊇ E`.
- `C2inc_(−1) ⊆ μ^(-1) E ∖ E`. On `C2inc_(−1)`:
  - `n_(−2) n_0 <= n_(−1)²` puts `v` outside `E`;
  - `n_(−1)² < n_(−2) n_1 < n_(−2)(n_0 + n_1)` puts `v` inside `μ^(-1) E`.
- Apply (T1).

**(4b) `Q(C1inc_0) <= t_μ + t_ρ + Q(bad_0)`.** Take `E = {i >= 1, n_(−1) < n_0, n_0² > n_(−1) n_1}`.
- `ρ^(-1) E = {n_0 < n_1, n_1² > n_0 n_2}`. The pointer of `ρv` is always `>= 1`.
- `μ^(-1) E = {i >= 1, n_(−1) < n_0 + n_1, (n_0 + n_1)² > n_(−1) n_2}`.
- *`C1inc_0 ⊆ μ^(-1) E ∖ ρ^(-1) E`.* On `C1inc_0`, `n_1² <= n_0 n_2` puts `v` outside `ρ^(-1) E`. Also
  `n_(−1) < n_0 < n_0 + n_1` and `n_(−1) n_2 < n_1² < (n_0 + n_1)²`, so `v` is in `μ^(-1) E`.
- *`ρ^(-1) E ∖ μ^(-1) E ⊆ bad_0`.* Let `v` be in `ρ^(-1) E` but not in `μ^(-1) E`. If `i = 0`, then `v ∈ bad_0`.
  If `i >= 1`, then `n_0 < n_1`, `n_1² > n_0 n_2`, and one of the following holds:
  - `n_(−1) >= n_0 + n_1 > n_0`;
  - `n_(−1) >= (n_0 + n_1)²/n_2 > (n_0 + n_1)² n_0/n_1² > n_0`.
  In both cases `n_0 < min(n_(−1), n_1)`, a weak local minimum. By the local step `v ∈ C1_0 ∪ C2_0`.
- Apply (T2).

**(4c) `Q(C1dec_1) <= t_μ + t_ρ`.** Take `E = {n_0 n_2 > n_1²}`, that is `{z_0 > z_1}`.
- `ρ^(-1) E = {n_1 n_3 > n_2²}` and `μ^(-1) E = {(n_0 + n_1) n_3 > n_2²}`. So `ρ^(-1) E ⊆ μ^(-1) E`.
  - In logarithmic form, `z'_0 = z_0 + z_1 + λ` with `λ = log(1 + n_1/n_0) > 0` and `z'_1 = z_2`.
- *`C1dec_1 ⊆ μ^(-1) E ∖ ρ^(-1) E`.* On `C1dec_1`, `n_1 n_3 <= n_2²` puts `v` outside `ρ^(-1) E`, and
  `n_2² < n_0 n_3 < (n_0 + n_1) n_3` puts `v` inside `μ^(-1) E`.
- Apply (T2) with an empty error term.

**(4d) `Q(C2dec_0) <= t_μ + Q(bad_1)`.** Take `E = {i >= 1, n_0 > n_1, n_(−1) n_1 < n_0²}`.
- `μ^(-1) E = {i >= 1, n_0 + n_1 > n_2, n_(−1) n_2 < (n_0 + n_1)²}`.
- *`C2dec_0 ⊆ μ^(-1) E ∖ E`.* On `C2dec_0 ⊆ A^dec_0 = {i >= 1, n_(−1) > n_0 > n_1 > n_2}`:
  - `n_0² <= n_(−1) n_1` puts `v` outside `E`;
  - `n_0 + n_1 > n_2` and `n_(−1) n_2 < n_0² < (n_0 + n_1)²` put `v` inside `μ^(-1) E`.
- *`E ∖ μ^(-1) E ⊆ bad_1`.* On `E ∖ μ^(-1) E` we have `n_0 > n_1`, and one of the following holds:
  - `n_2 >= n_0 + n_1 > n_1`;
  - `n_2 >= (n_0 + n_1)²/n_(−1) > (n_0 + n_1)² n_1/n_0² > n_1`.
  So `n_1 < min(n_0, n_2)`, and by the local step `v ∈ C1_1 ∪ C2_1`.
- Apply (T1').

**Remark (why the signs are favourable).** Under `μ`, `y_(−1)` becomes `y_(−1) + λ`, `y_0` becomes `y_1 − δ`
(with `δ = log(1 + n_0/n_1)`), and `y_j` becomes `y_(j+1)` for `j >= 1`. In `z`-form, `z_(−1)` becomes
`z_(−1) − λ` and `z_0` becomes `z_0 + z_1 + λ`.

Each test event compares a slot pushed up with a slot pushed down (or left unchanged), in the direction that
enlarges the event. The only failures of inclusion are the orientation-reversing configurations, and those are
level-0 local minima.

## Step 5. Summing the level-1 tests

Let `bad1_k = C1inc_k ∪ C2inc_k ∪ C1dec_k ∪ C2dec_k`. By Step 4 and the shift rule, with base offsets `0, −1, 1, 0`:

`Q(bad1_k) <= (t_μ + t_ρ + Q(bad_0) + |k| t_ρ) + (t_μ + |k+1| t_ρ) + (t_μ + t_ρ + |k−1| t_ρ) + (t_μ + Q(bad_1) + |k| t_ρ)`.

Use `Q(bad_0) <= 2 t_μ + 3 t_ρ`, `Q(bad_1) <= 2 t_μ + 4 t_ρ` and `|k+1| + |k−1| <= 2|k| + 2`. This gives
`Q(bad1_k) <= 8 t_μ + 11 t_ρ + 4|k| t_ρ`, which is Claim item 1.

## Step 6. Tent lemma for positive reals

**Lemma.** Let `m >= 3` and let `x_1, ..., x_m > 0` be real, with `(x_(k−1), x_k, x_(k+1)) ∉ C1 ∪ C2` for
`2 <= k <= m − 1`. Suppose every consecutive pair has `max(x_k, x_(k+1)) >= c > 0`. Then
`max_k x_k >= c F(⌈(m−1)/2⌉)`, where `F(1) = F(2) = 1`.

*Proof.* Let `p` be the first index where the maximum is attained.

*Left of `p`.* Suppose `p >= 2`. Then `x_(p−1) < x_p`, because `p` is the first maximum. For
`k = p−1, p−2, ..., 2`, in turn, `x_k < x_(k+1)`, so the local step gives `x_(k−1) < x_k` and
`x_(k+1) >= x_k + x_(k−1)`. Hence `x_1 < x_2 < ... < x_p` with `x_(k+1) >= x_k + x_(k−1)` for `2 <= k <= p−1`.
- `x_2 >= c`, since `x_2 > x_1` and the pair `(x_1, x_2)` has maximum `>= c`.
- `x_3 >= x_2 + x_1 >= c`.
- By induction, `x_s >= F(s−1) c` for `2 <= s <= p`.
- So `x_p >= F(p−1) c`.

*Right of `p`.* Suppose `p <= m − 1`. Then `x_(p+1) <= x_p`.
- If `p >= 2` and `x_(p+1) = x_p`, the local step at `k = p` gives `x_(p+1) >= x_(p−1) + x_p > x_p`, which is
  impossible. So `x_(p+1) < x_p` whenever `p >= 2`. If `p = 1`, only `x_2 <= x_1` is used.
- For `k = p+1, ..., m−1`, in turn, `x_k <= x_(k−1)`, so the mirror step gives `x_(k+1) < x_k` and
  `x_(k−1) >= x_k + x_(k+1)`.
- Then `x_(m−1) > x_m` gives `x_(m−1) >= c`, and `x_(m−2) >= x_(m−1) + x_m >= c`.
- By induction, `x_(m−s) >= F(s) c` for `1 <= s <= m − p`. So `x_p >= F(m−p) c`.

*Conclusion.* Since `max(p − 1, m − p) >= (m−1)/2`, and `F` is nondecreasing, `x_p >= c F(⌈(m−1)/2⌉)`. When
`p = 1` or `p = m`, only the side that exists is used, and it has length `m − 1`. ∎

**Pair bound.** Let `n_(k+1) >= n_k + n_(k−1)` with all terms positive, and put `r = n_(k+1)/n_k` and
`r' = n_k/n_(k−1)`. Then `r >= 1 + 1/r'`. So if `r' < φ`, then `r > 1 + 1/φ = φ`. Hence `max(r, r') >= φ`, and
the two consecutive log-ratios have maximum `>= log φ`. The mirror statement holds for `n_(k−1) >= n_k + n_(k+1)`
and the ratios `n_(k−1)/n_k`, `n_k/n_(k+1)`.

## Step 7. Doubly exponential run lemma (Claim item 2)

Let `K >= 3`, and let `v` avoid `bad_j` and `bad1_j` for all `|j| <= K − 1`. Avoiding `bad_(−K+1)` gives
`i >= K`, so `n_j` is defined for `|j| <= K`. Every level-1 event at offset `k >= −K+1` has its pointer condition
`i + k − 1 >= 0` satisfied.

**Case `n_0 <= n_1`.** The local step at `k = 0` gives `n_(−1) < n_0` and `n_1 >= n_(−1) + n_0`. Then
`n_(−1) <= n_0` lets it run at `k = −1`, and so on down to `k = −K+1`. This gives
`n_(−K) < ... < n_0 < n_1` with `n_(k+1) >= n_k + n_(k−1)` for `−K+1 <= k <= 0`.
- The `K + 1` log-ratios `y_(−K), ..., y_0` are positive.
- For `−K+1 <= k <= −1`, the indices `k−1, ..., k+2` lie in `[−K, 1]`, so `v ∈ A^inc_k`. Since
  `v ∉ C1inc_k ∪ C2inc_k`, the triple `(y_(k−1), y_k, y_(k+1))` is not in `C1 ∪ C2`.
- By the pair bound, each consecutive pair `(y_(k−1), y_k)`, `−K+1 <= k <= 0`, has maximum `>= log φ`.
- By the tent lemma with `m = K + 1`, some `y_j >= log φ · F(⌈K/2⌉)`. Hence
  `n_(j+1) >= n_(j+1)/n_j >= φ^(F(⌈K/2⌉))`, with `|j + 1| <= K`.

**Case `n_0 > n_1`.** The mirror step at `k = 1, ..., K−1` gives `n_0 > n_1 > ... > n_K` with
`n_(k−1) >= n_k + n_(k+1)`.
- The `K` log-ratios `z_0, ..., z_(K−1)` are positive.
- For `1 <= k <= K − 2`, we have `v ∈ A^dec_k` and `v ∉ C1dec_k ∪ C2dec_k`. So the `z`-triples at interior
  positions avoid `C1 ∪ C2`.
- By the pair bound, each consecutive pair has maximum `>= log φ`.
- By the tent lemma with `m = K >= 3`, some `n_j >= n_j/n_(j+1) >= φ^(F(⌈(K−1)/2⌉))`, with `0 <= j <= K − 1`.

In both cases some tree within distance `K` of the pointer has at least `φ^(F(⌈(K−1)/2⌉))` leaves.

## Step 8. Profile (Claim item 3)

`G1_K` is the complement of `∪_(|j|<=K−1) (bad_j ∪ bad1_j)`. By Steps 3 and 5, with
`Σ_(|j|<=K−1) |j| = K(K−1)`:
- `Σ_j Q(bad_j) <= (2K−1)(2 t_μ + 3 t_ρ) + K(K−1) t_ρ`;
- `Σ_j Q(bad1_j) <= (2K−1)(8 t_μ + 11 t_ρ) + 4K(K−1) t_ρ`.

The total is `(20K − 10) t_μ + (5K² + 23K − 14) t_ρ <= (5K² + 23K)(t_μ + t_ρ) <= 2√2 (5K² + 23K) √η`.

## Step 9. Corollaries

**Cutoff kill.** Under the hypothesis, `G1_K` is `Q`-null by Step 7. So `1 <= 2√2 (5K² + 23K) √η`, that is
`η >= 1/(8(5K² + 23K)²)`.

For a cutoff `N >= 3`, let `m = ⌈log_φ log_φ N⌉ + 3` and `K = 2m + 1 <= 2 log_φ log_φ N + 9`.
- `F(s) >= φ^(s−2)`, so `F(⌈(K−1)/2⌉) = F(m) >= φ · log_φ N > log_φ N`.
- Hence every tree of at most `N` leaves has fewer than `φ^(F(m))` leaves, and the hypothesis holds at this `K`.
- This gives `η >= 1/(8(5K² + 23K)²) >= c/(1 + log log N)^4` for an absolute `c > 0`.

**Size of nearby trees.** For `K >= 1`, `5K² + 23K <= 28K²`. With `K = floor((112√2 √η)^(−1/2))`, Step 8 gives
`Q(R ∖ G1_K) <= 56√2 K² √η <= 1/2`.
- If `K >= 3`, Step 7 applies on `G1_K`, which has mass at least `1/2`.
- The size bound is `φ^(F(⌈(K−1)/2⌉)) >= φ^(φ^((K−5)/2))`.

**Log-ratio turning-point kill.** On `A^inc_0` the triple `(y_(−1), y_0, y_1)` is positive. By the local step, a
weak local minimum in the middle puts `v` in `C1inc_0 ∪ C2inc_0`.
- By (4b), (4a) and the shift rule, `p1 <= (3 t_μ + 4 t_ρ) + (t_μ + t_ρ) <= 5(t_μ + t_ρ) <= 10√2 √η`.
- Suppose the conditional law of the three ratios on `A^inc_0` is exchangeable, and `Q(A^inc_0) = π`. The three
  events "coordinate `r` is a weak minimum" cover the space and have equal probability, so each has probability
  `>= 1/3`. Then `p1 >= π/3` and `η >= π²/1800`.

## Step 10. Audit

`loglevel_check.py` Part A checks, on all 823543 tuples `(n_(−2), ..., n_4) ∈ [1, 7]^7` and on 300000 random
tuples with entries up to `10^7`:
- the eight inclusions of Step 4;
- one instance of the shift rule.

The moves are applied literally to the tuple, so the pull-back formulas of Step 2 are tested as well. All
arithmetic is exact integer arithmetic. There were no failures.

The level-1 events are non-vacuous. On `[1, 6]^7`, each occurs 864 to 1512 times.

Part B finds, for `K = 2, 3, 4`, the smallest possible maximum of a window that is good at levels 0 and 1 at all
interior positions. The results are `3, 7, 16`, against the proved bound `φ^(F(⌈(K−1)/2⌉))`. The bound is weak
for small `K`; the doubly exponential regime starts only at large `K`. The output is `loglevel_check.out`.
