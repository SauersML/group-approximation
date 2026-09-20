---
rg: 2
id: thompson-f-near-eigenvectors-have-fibonacci-tree-profiles
kind: claim
title: Every near-eigenvector of Thompson's F on one-sided pointed forests sees, within distance K of its pointer, a super-Fibonacci monotone run of tree sizes and a tree with at least F_(K+2) leaves, with failure mass at most 2√2(K²+5K)√η; so tree-size cutoffs N cost at least 1/(8(K²+5K)²) with K ≈ log_φ N, for every amplitude
distinct_from:
  thompson-f-one-sided-forest-windows-are-norm-lossless: that proves the support E(S_n) is lossless and that pointer-leaf and pointer-at-root mass must vanish; this proves a quantitative profile constraint on every amplitude, which kills any tree-size cutoff at a polylogarithmic rate and any family with turning points of positive mass.
  thompson-f-iid-forest-test-vectors-are-bounded-below-one: that caps product-form vectors via a Hellinger idempotence gap; this uses no product structure. Its invariant is the turning-point mass of the size profile, and it applies to correlated, Markov and hierarchical amplitudes alike.
  thompson-f-product-forest-vectors-stay-below-71-72: that is a sharper numerical cap (71/72) for the product class only; this is a weaker cap for a class containing every amplitude with positive turning-point mass.
  thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit: that is numerical and in a formal log-scale limit; this is rigorous at every finite size, has no stationarity assumption, and explains why size profiles must be unimodal with super-Fibonacci runs.
  thompson-f-is-amenable: the root is untouched; this is a necessary structure for any Følner-type vector in the lossless forest model.
artifacts:
  - experiments/thompson-f-tree-profile-2026-09-17/profile_check.py
  - experiments/thompson-f-tree-profile-2026-09-17/profile_check.out
---

**ESTABLISHED** by `thompson-f-near-eigenvectors-have-fibonacci-tree-profiles-proof` (direct proof, not refereed;
no priority claimed).

**Setting.** This is the one-sided forest model of `thompson-f-one-sided-forest-windows-are-norm-lossless`, item 3.
- `R` is the set of pointed forests `v = (T_0, T_1, ...; i)` with finitely many nontrivial trees and `i >= 0`.
- `ρ(v) = (T_0, ...; i+1)` moves the pointer right. `μ(v)` merges `T_i` and `T_(i+1)` into `(T_i, T_(i+1))`
  and shifts the later trees left. Both are injective, and their edges are all the edges of `Γ_R`.
- For a unit `f >= 0` on `R`: `Q = f²`, `⟨f, K f⟩ = 2 Σ f(v) f(ρv) + 2 Σ f(v) f(μv)`, and
  `η(f) = 1 − ⟨f, K f⟩/4`. By item 1 there, `inf_f η(f) = 1 − ||P||`, so `F` is amenable iff `inf η = 0`.
- `n_j(v)` is the number of leaves of `T_(i+j)` (defined for `j >= −i`). `F_k` are the Fibonacci numbers,
  `F_1 = F_2 = 1`.
- Say `v` is **bad at offset `j`** if `i + j <= 0`, or, with `(a, b, c) = (n_(j−1), n_j, n_(j+1))`,
  `b <= c < a + b` (C1) or `b <= a < b + c` (C2). Every weak local minimum `a >= b <= c` is bad (C1 or C2),
  since otherwise `c >= a + b` and `a >= b + c` would give `c > c`.

**Theorem.** For every unit `f >= 0` on `R` and every `K >= 2`:
1. **(Merge test events.)** `Q(v bad at offset 0) <= 2 t_μ + 3 t_ρ <= 6√2 √η`. Here `t_g = TV(Q, g_*Q)` and
   `t_μ + t_ρ <= 2√2 √η`.
2. **(Run lemma, deterministic.)** Let positive integers `x_(−K), ..., x_K` have no bad offset in `[−K+1, K−1]`
   (conditions C1, C2 only). Then they contain a strictly monotone run of at least `K+1` terms with
   `x_(k+1) >= x_k + x_(k−1)` along it, and `max x >= F_(K+2)`. This bound is sharp.
3. **(Profile theorem.)** `Q( i >= K and some tree T_(i+j), |j| <= K, has >= F_(K+2) leaves ) >= 1 − 2√2 (K² + 5K) √η`.

**Corollaries.**
- **(Cutoff kill.)** Suppose `Q`-a.s. every tree within distance `K` of the pointer has fewer than `F_(K+2)`
  leaves. Then `⟨f, P f⟩ <= 1 − 1/(8(K² + 5K)²)`.
  - For a cutoff `N`, take `K` minimal with `F_(K+2) > N`, so `K <= log_φ N + 1`. Then
    `1 − ⟨f, P f⟩ >= c/(log N)^4`, for every amplitude supported on trees of at most `N` leaves near the pointer.
  - The trivial orbit bound (`μ^N f ⊥ f`) gives only `1/(2N²)`. This is exponentially better in `N`.
  - Contrapositive: a vector with `1 − ⟨f,Pf⟩ = η` puts mass `>= 1/2` on configurations with a tree of
    `>= F_(K+2) ≈ φ^K` leaves within distance `K` of the pointer, for `K ≈ (32 η)^(−1/4)`. So its nearby trees
    have size at least `exp(c η^(−1/4))`.
- **(Turning-point kill.)** Let `p = Q(i = 0, or the pointer tree is a weak local minimum of the size profile)`.
  Then `⟨f, P f⟩ <= 1 − p²/72`.
  - The invariant is the **turning-point mass**. The dying step is the pair of merge test events
    `{n_0 > n_1}` and `{n_(−1) < n_0}`: merging raises their probability by exactly the C1 and C2 masses.
  - Any family whose pointer triple is exchangeable in law has `p >= 1/3`, so it is capped at `1 − 1/648`.
  - This covers correlated and hierarchical amplitudes that product and Markov ceilings do not. Any family
    whose size profile has turning points of positive mass near the pointer is dead as a route to `||P|| = 1`.

**What it changes.** The lossless node left "the amplitude class" as the only possible loss. This theorem names
the shape a Følner-type amplitude must take in `R`: near the pointer, the tree sizes form a unimodal profile
(a "tent") whose sides grow at least like Fibonacci numbers, with turning points of vanishing mass. Numerical
ansätze with a fixed size cutoff, or with i.i.d.-like local size statistics, cannot approach 1. A new ansatz has
to be built on super-Fibonacci tents.

**Checks.** `profile_check.py` (output `profile_check.out`) checks:
- (A) by exhaustive DFS for `K = 2..6`: no good window has entries `< F_(K+2)`, and the bound is attained;
- (B) on Perron vectors of the windows `W_n`, `n = 4..8`, and 20 random perturbations each: the three
  inequalities of item 1 and the shift bound. The printed `ρ_n/4 = 0.7075, 0.7372` at `n = 6, 7` reproduce the
  lossless node's table, which confirms that the model is identified correctly.

## Attempts
