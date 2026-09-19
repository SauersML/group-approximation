---
rg: 2
id: thompson-f-near-eigenvectors-have-fibonacci-tree-profiles-proof
kind: route
title: Hellinger control of the two moves, two merge test events, a shift bound and a deterministic super-Fibonacci run lemma
target: thompson-f-near-eigenvectors-have-fibonacci-tree-profiles
requires: []
artifacts:
  - experiments/thompson-f-tree-profile-2026-09-17/profile_check.py
  - experiments/thompson-f-tree-profile-2026-09-17/profile_check.out
---

**Conventions.** These are those of `thompson-f-one-sided-forest-windows-are-norm-lossless`, items 1, 3 and 4.
- `R` is the set of one-sided pointed forests `v = (T_0, T_1, ...; i)`. `Γ_R` is the compression of the Cayley graph
  of `F` to `R`.
- `ρ(v) = (T_0, T_1, ...; i+1)`. It is a bijection `R -> {i >= 1}`, and its inverse is "pointer left".
- `μ(v)` replaces `T_i, T_(i+1)` by the single tree `(T_i, T_(i+1))` and shifts `T_(i+2), ...` one place left. It is
  a bijection `R -> {T_i not a leaf}`, and its inverse is "split".
- By item 3 there, every edge of `Γ_R` is `{v, ρv}` or `{v, μv}`, each counted once from each end. So for `f >= 0`,
  `⟨f, K f⟩ = 2 Σ_v f(v) f(ρv) + 2 Σ_v f(v) f(μv)`.
- By item 3 there, `sup ⟨f, K f⟩ = ||K|| = 4||P||` over unit `f` on `R`. Since `K` has nonnegative entries, we may
  take `f >= 0`. Write `⟨f, P f⟩ := ⟨f, K f⟩ / 4` and `η = 1 − ⟨f, P f⟩`. Then `||P|| = 1 − inf_f η(f)`.
- `Q = f²` is a probability measure on `R`. `n_j(v)` is the number of leaves of `T_(i+j)`, defined for `j >= −i`.

## Step 1. Hellinger control of the two moves

For `g ∈ {ρ, μ}`, `g` is injective, so `g_*Q(gv) = Q(v)` and `g_*Q` is a probability measure. Its Bhattacharyya
coefficient with `Q` is
`BC_g = Σ_w sqrt(Q(w) g_*Q(w)) = Σ_v f(gv) f(v)`.
Hence `⟨f, P f⟩ = (BC_ρ + BC_μ)/2` and `η = ((1 − BC_ρ) + (1 − BC_μ))/2`.

Let `t_g = TV(Q, g_*Q)`. The classical Hellinger–TV inequality `TV <= sqrt(1 − BC²)` gives
`t_g <= sqrt(2(1 − BC_g))`. By Cauchy–Schwarz,
`t_ρ + t_μ <= sqrt(2) (sqrt(1 − BC_ρ) + sqrt(1 − BC_μ)) <= 2 sqrt(1 − BC_ρ + 1 − BC_μ) = 2√2 √η`.

For every event `E` and each `g`, `|Q(g^(-1) E) − Q(E)| = |g_*Q(E) − Q(E)| <= t_g`.

## Step 2. Pull-backs of the size coordinates

Directly from the definitions, for every `v` and every `j` for which the right-hand side is defined:
- `n_j(ρv) = n_(j+1)(v)`, and the pointer of `ρv` is `i + 1`;
- `n_0(μv) = n_0(v) + n_1(v)`;
- `n_j(μv) = n_(j+1)(v)` for `j >= 1`;
- `n_j(μv) = n_j(v)` for `−i <= j <= −1`, and the pointer of `μv` is `i`.

## Step 3. The merge test events (Theorem item 1)

For `j >= 1 − i`, write `(a, b, c) = (n_(j−1), n_j, n_(j+1))`. Let `C1_j = {b <= c < a + b}` and
`C2_j = {b <= a < b + c}`. Let `bad_j = {i + j <= 0} ∪ C1_j ∪ C2_j`.

- **(a) Pointer at the root.** `ρ_*Q` is supported on `{i >= 1}`, so `Q(i = 0) = Q(i=0) − ρ_*Q(i=0) <= t_ρ`.
- **(b) Event `E2 = {i >= 1, n_(−1) < n_0}`.** By Step 2, `μ^(-1) E2 = {i >= 1, n_(−1) < n_0 + n_1}`. So
  `Q(μ^(-1) E2) − Q(E2) = Q(i >= 1, n_0 <= n_(−1) < n_0 + n_1) = Q(C2_0 ∩ {i >= 1})`. Hence
  `Q(C2_0 ∩ {i >= 1}) <= t_μ`.
- **(c) Event `E1 = {n_0 > n_1}`.**
  - By Step 2, `μ^(-1) E1 = {n_0 + n_1 > n_2}` and `ρ^(-1) E1 = {n_1 > n_2}`.
  - Therefore `Q(n_0 + n_1 > n_2) − Q(n_0 > n_1) <= t_μ` and `Q(n_0 > n_1) − Q(n_1 > n_2) <= t_ρ`.
  - Since `{n_1 > n_2} ⊆ {n_0 + n_1 > n_2}`, the difference of the outer two events is
    `{n_1 <= n_2 < n_0 + n_1} = C1_1`. So `Q(C1_1) <= t_μ + t_ρ`.
  - By Step 2, `ρ^(-1)(C1_0 ∩ {i >= 1}) = C1_1`, where every `v` qualifies because `ρv` has pointer `>= 1`. So
    `Q(C1_0 ∩ {i >= 1}) <= Q(C1_1) + t_ρ <= t_μ + 2 t_ρ`.
- **(d) Sum.** `Q(bad_0) <= t_ρ + t_μ + (t_μ + 2 t_ρ) = 2 t_μ + 3 t_ρ <= 3(t_μ + t_ρ) <= 6√2 √η`.

## Step 4. Shift bound

By Step 2, `ρ^(-1)(bad_j) = bad_(j+1)` exactly: `i + 1 + j <= 0` iff `i + (j+1) <= 0`, and the triple of sizes of
`ρv` at offset `j` is the triple of `v` at offset `j + 1`. So `|Q(bad_(j+1)) − Q(bad_j)| <= t_ρ` for every
integer `j`, and `Q(bad_j) <= Q(bad_0) + |j| t_ρ`.

## Step 5. The run lemma (Theorem item 2)

**Local step.** Let positive integers `(a, b, c)` satisfy neither `C1` nor `C2`.
- If `b <= c`, then `a < b` and `c >= a + b`. Indeed, not C1 forces `c >= a + b`. If moreover `a >= b`, then not C2
  forces `a >= b + c > c >= a + b > a`, a contradiction.
- If `b <= a`, then `c < b` and `a >= b + c`. This is the mirror statement.
- In particular, `(a, b, c)` is not a weak local minimum.

**Induction.** Let `x_(−K), ..., x_K` (`K >= 2`) have no C1 or C2 at any offset `k ∈ [−K+1, K−1]`, meaning the
triple `(x_(k−1), x_k, x_(k+1))`.
- *Case `x_0 <= x_1`.* The local step at `k = 0` gives `x_(−1) < x_0` and `x_1 >= x_(−1) + x_0`. Then
  `x_(−1) <= x_0` lets the local step run at `k = −1`, and so on down to `k = −K+1`. This yields
  `x_(−K) < x_(−K+1) < ... < x_0 < x_1` with `x_(k+1) >= x_k + x_(k−1)` for `k = −K+1, ..., 0`.
  - From `x_(−K) >= 1` and `x_(−K+1) >= 2` we get `x_(−K+m) >= F_(m+2)`, so `x_1 >= F_(K+3)`. The run has
    `K + 2` terms.
- *Case `x_0 > x_1`.* The mirror step at `k = 1, 2, ..., K−1` gives `x_0 > x_1 > ... > x_K` with
  `x_(k−1) >= x_k + x_(k+1)`.
  - From `x_K >= 1` and `x_(K−1) >= 2` we get `x_(K−m) >= F_(m+2)`, so `x_0 >= F_(K+2)`. The run has `K + 1` terms.
- In both cases `max x >= F_(K+2)`. It is sharp: `x_j = F_(K+2−j)` for `j >= 0`, together with a suitable left
  part, is a good window with maximum `F_(K+2)`. Part A of `profile_check.py` confirms by exhaustive DFS, for
  `K = 2..6`, that there is no good window with all entries `<= F_(K+2) − 1`, and exactly one with all entries
  `<= F_(K+2)`.

## Step 6. Profile theorem (Theorem item 3)

Let `G_K` be the set of `v` that are not bad at any offset `j ∈ [−K+1, K−1]`.
- On `G_K`, not being bad at `j = −K+1` gives `i >= K`. So `x_j = n_j(v)`, `|j| <= K`, are defined positive
  integers with no C1 or C2 at interior offsets. By Step 5 some `T_(i+j)`, `|j| <= K`, has `>= F_(K+2)` leaves.
- By Steps 3 and 4, with `Σ_(|j|<=K−1) |j| = K(K−1)`:
  `Q(R ∖ G_K) <= (2K−1)(2 t_μ + 3 t_ρ) + K(K−1) t_ρ = (4K−2) t_μ + (K² + 5K − 3) t_ρ`.
  This is at most `(K² + 5K)(t_μ + t_ρ) <= 2√2 (K² + 5K) √η`, since `4K − 2 <= K² + 5K` for `K >= 1`.

## Step 7. Corollaries

- **Cutoff kill.** If `Q`-a.s. no tree within distance `K` of the pointer has `>= F_(K+2)` leaves, then `G_K` is
  `Q`-null. So `1 <= 2√2 (K² + 5K) √η`, that is `η >= 1/(8(K² + 5K)²)`.
  - For a cutoff `N >= 2`, let `K >= 2` be minimal with `F_(K+2) > N`. Then either `K = 2`, or `F_(K+1) <= N`.
    Since `F_(K+1) >= φ^(K−1)`, this gives `K <= log_φ N + 1`, and `η >= c/(log N)^4` with an absolute `c > 0`.
  - For comparison, the trivial orbit bound. Let `u f = f∘μ^(-1)`, supported on `μ(R)`. If the pointer tree has
    `<= N` leaves `Q`-a.s., then `u^N f` is supported where the pointer tree has `> N` leaves, so `u^N f ⊥ f`.
    Then `2 = ||f − u^N f||² <= N² ||f − u f||² = 2N²(1 − BC_μ) <= 4N² η`, which gives only `η >= 1/(2N²)`.
- **Size of nearby trees.** Choose `K` with `2√2 (K² + 5K) √η <= 1/2`. Then `Q(G_K) >= 1/2`, and `F_(K+2) >= φ^K`.
  Since `K² + 5K <= 6K²`, one may take `K = floor((24√2 √η)^(−1/2))`, which is of order `η^(−1/4)`.
- **Turning-point kill.** Let `p = Q(i = 0, or i >= 1 and n_0 <= min(n_(−1), n_1))`. By the local step, a weak
  local minimum at offset 0 lies in `C1_0 ∪ C2_0`. So `p <= Q(bad_0) <= 6√2 √η`, that is `η >= p²/72`.
  - Suppose that, conditionally on `i >= 1`, the law of `(n_(−1), n_0, n_1)` is exchangeable. Then some coordinate
    attains the minimum, and by symmetry the middle one does with conditional probability `>= 1/3`. So
    `p >= Q(i=0) + Q(i>=1)/3 >= 1/3`, and `⟨f, P f⟩ <= 1 − 1/648`.

## Step 8. Numerical audit

Part B of `profile_check.py` builds the Perron vectors of the move graph on `W_n`, `n = 4..8`, together with 20
lognormal perturbations each. For each vector it checks:
- `Q(bad_0) <= 2 t_μ + 3 t_ρ`;
- `t_μ + t_ρ <= 2√2 √η`;
- `Q(bad_j) <= Q(bad_0) + |j| t_ρ` for `|j| <= 3`.

The Perron values `ρ_n/4 = 0.7075` at `n = 6` and `0.7372` at `n = 7` match the table in
`thompson-f-one-sided-forest-windows-are-norm-lossless`. The output is `profile_check.out`, and every line reads OK.
