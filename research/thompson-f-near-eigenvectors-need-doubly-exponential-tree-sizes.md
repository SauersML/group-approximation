---
rg: 2
id: thompson-f-near-eigenvectors-need-doubly-exponential-tree-sizes
kind: claim
title: Near-eigenvectors of Thompson's F on pointed forests see doubly exponential trees - multiplicative merge tests on log-ratios force a super-Fibonacci run of log size ratios at distance O(eta^(-1/4))
distinct_from:
  thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit: that is numerical saturation of one test-vector family with no rigorous ceiling; this proves a rigorous deficit for every unit vector whose trees near the pointer stay below a doubly exponential size, and says nothing about the value 0.977.
  thompson-f-one-sided-forest-windows-are-norm-lossless: that is the exact compression identity ||K|| = 4||P|| on pointed forests, used here as the setting; this is a structure theorem for near-optimal vectors on that model.
  thompson-f-folner-function-dominates-every-ackermann-level: that bounds the size of Følner sets of F from below; this is a spectral, local statement - most of the mass of any vector with deficit eta sits on forests with a doubly exponential tree within distance O(eta^(-1/4)) of the pointer, with explicit constants - and neither statement implies the other.
  thompson-f-is-amenable: that is the open root; this constrains near-eigenvectors quantitatively and decides nothing.
artifacts:
  - experiments/thompson-f-doubly-exponential-profile-2026-09-17/loglevel_check.py
  - experiments/thompson-f-doubly-exponential-profile-2026-09-17/loglevel_check.out
---

**Setting.** This is the model of `thompson-f-one-sided-forest-windows-are-norm-lossless`.
- `R` is the set of one-sided pointed forests `v = (T_0, T_1, ...; i)`.
- `ρ` moves the pointer right. `μ` merges `T_i` and `T_(i+1)` into one tree.
- For unit `f >= 0` on `R`, `η = 1 − ⟨f, P f⟩`. `||P|| = 1 − inf_f η(f)`, so `F` is amenable iff `inf η = 0`.
- `Q = f²`. `n_j(v)` is the number of leaves of `T_(i+j)`.

Level-0 goodness is the merge-test notion of the wave-17 Fibonacci profile theorem, reproved here. A triple
`(a, b, c)` is in `C1` if `b <= c < a + b`, and in `C2` if `b <= a < b + c`.

**Level-1 events.** On increasing stretches, put `y_j = log(n_(j+1)/n_j)`. On decreasing stretches, put
`z_j = log(n_j/n_(j+1))`.
- `A^inc_k = {i + k − 1 >= 0, n_(k−1) < n_k < n_(k+1) < n_(k+2)}`, and `A^dec_k` is the same with all
  inequalities reversed.
- `C1inc_k = A^inc_k ∩ {(y_(k−1), y_k, y_(k+1)) ∈ C1}` and `C2inc_k = A^inc_k ∩ {(y_(k−1), y_k, y_(k+1)) ∈ C2}`.
  `C1dec_k` and `C2dec_k` are the same with `z` and `A^dec_k`.
- `bad1_k` is the union of the four.

**Claim (ESTABLISHED).** Let `t_ρ, t_μ` be the total variation distances `TV(Q, ρ_*Q)` and `TV(Q, μ_*Q)`, so that
`t_ρ + t_μ <= 2√2 √η`.

1. **Multiplicative merge tests.** Let `bad_j` be the level-0 bad event.
   - `Q(C2inc_(−1)) <= t_μ`.
   - `Q(C1inc_0) <= t_μ + t_ρ + Q(bad_0)`.
   - `Q(C1dec_1) <= t_μ + t_ρ`.
   - `Q(C2dec_0) <= t_μ + Q(bad_1)`.
   - Each family moves by at most `t_ρ` per unit shift of `k`.
   - Hence `Q(bad1_k) <= 8 t_μ + 11 t_ρ + 4|k| t_ρ`.
2. **Doubly exponential run lemma.** Suppose `K >= 3` and `v` is good at levels 0 and 1 at every offset in
   `[−K+1, K−1]`. Then `i >= K`, and some tree `T_(i+j)` with `|j| <= K` has at least `φ^(F(⌈(K−1)/2⌉))`
   leaves. Here `F(m)` is the Fibonacci number and `φ` is the golden ratio.
   - The mechanism: on an increasing run with `n_(k+1) >= n_k + n_(k−1)`, every pair of consecutive log-ratios has
     maximum at least `log φ`.
   - Level-1 goodness makes the log-ratios themselves a tent with a super-Fibonacci monotone run.
3. **Profile.** Let `G1_K` be the set of `v` good at levels 0 and 1 at every offset `|k| <= K − 1`. Then
   `Q(R ∖ G1_K) <= (5K² + 23K)(t_μ + t_ρ) <= 2√2 (5K² + 23K) √η`.

**Corollaries.**
- **Cutoff kill (doubly logarithmic).** Suppose `Q`-a.s. every tree within distance `K` of the pointer has fewer
  than `φ^(F(⌈(K−1)/2⌉))` leaves. Then `η >= 1/(8(5K² + 23K)²)`.
  - In particular, if every tree within distance `2 log_φ log_φ N + 9` of the pointer has at most `N` leaves
    (`N >= 3`), then `η >= c/(1 + log log N)^4`.
  - Wave 17 had `c/(log N)^4`, and the trivial orbit bound is `1/(2N²)`.
- **Size of nearby trees.** With `K = floor((112√2 √η)^(−1/2))`, which is of order `η^(−1/4)`, at least half of
  the mass of `Q` sees, within distance `K` of the pointer, a tree with at least
  `φ^(φ^((K−5)/2)) = exp(exp(c η^(−1/4)))` leaves.
- **Log-ratio turning-point kill.** Let `p1 = Q(A^inc_0 ∩ {y_0 <= min(y_(−1), y_1)})`. This is the mass where the
  ratios of an increasing 4-window have a weak local minimum in the middle. Then `p1 <= 10√2 √η`, that is
  `η >= p1²/200`.
  - The class killed: every ansatz in which, on increasing 4-windows of mass `π`, the three consecutive ratios are
    exchangeable has `⟨f, P f⟩ <= 1 − π²/1800`.
  - An example is any vector under which consecutive size ratios `n_(j+1)/n_j` are i.i.d.: the event `A^inc_0`
    is symmetric in the three ratios, so exchangeability survives the conditioning.

**Route.** See `thompson-f-near-eigenvectors-doubly-exponential-proof`. It is self-contained and
reproves the level-0 merge tests.

**What is left: level 2 and tower growth.** Iterating once more takes log-ratios of the `y` on a monotone
level-1 run. It would give triply exponential sizes, and height `h` would give a tower of height `h + 1`.

The level-1 proof used two facts:
- a merge perturbs at most two log-ratio slots, one up by `+δ` and one down;
- the test events have exact multiplicative pull-backs.

At level 2, the merge perturbs three slots. With `w_j = log(y_(j+1)/y_j)`:
- `w'_(−2) = w_(−2) + w_(−1) + δ_2`;
- `w'_(−1) = w_0 − δ_2 + log(1 − δ/y_1)`;
- `w'_0 = w_1 + log(y_1/(y_1 − δ))`, where `δ = log(1 + n_0/n_1)`.

The level-1 argument does not control the sign pattern of this third slot in the C1 test. Closing this, for example by testing the
three-slot event directly or by absorbing the third perturbation into level-0 bad mass, is the next step toward a
tower-height profile of height about `log(1/η)`.
