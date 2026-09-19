---
rg: 2
id: thompson-f-matrix-product-forest-test-vectors
kind: claim
title: Correlated (matrix-product) forest test vectors for Thompson's F beat the split-form optimum only by an amount comparable to raising the tree cap about 1.3-fold, and every forest test vector is bounded by a size-level merge problem on stationary integer sequences whose value 1 is necessary for amenability
distinct_from:
  thompson-f-norm-bound-from-forest-renewal-test-vector: that certifies ||P|| > 0.9397 with a split-form (bond dimension 1) test vector; this extends the ansatz to bond dimension q with an exact matrix renewal DP and measures the gain from correlations in float only; it certifies no new bound.
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that is about expansion certificates (the non-amenable side) read through a finite tree automaton; the size-level relaxation here is an upper bound on Rayleigh quotients of test vectors (the amenable side) and reads the exact, unbounded tree sizes.
  thompson-f-exact-tail-observations-have-zero-defect: that is about shadow defects of flow observations; this is about Bhattacharyya coefficients of test-vector laws pushed forward to tree sizes.
artifacts:
  - experiments/thompson-f-forest-scaling-2026-09-17/mps_forest.py
  - experiments/thompson-f-forest-scaling-2026-09-17/opt_mps.py
  - experiments/thompson-f-forest-scaling-2026-09-17/opt_N9_q2.out
  - experiments/thompson-f-forest-scaling-2026-09-17/opt_N20_q2.out
  - experiments/thompson-f-forest-scaling-2026-09-17/opt_N40_q2.out
  - experiments/thompson-f-forest-scaling-2026-09-17/markov_size_level.py
  - experiments/thompson-f-forest-scaling-2026-09-17/markov_vs_iid_scan.py
  - experiments/thompson-f-forest-scaling-2026-09-17/scan.out
---

**OPEN.** The results are float scouting plus two short exact identities, stated below. No
interval certificate exists, and nothing here moves the certified bound 0.9397.

## Setting

We use the pointed-forest window model of `thompson-f-norm-bound-from-forest-renewal-test-vector`.

- States are `(T_0, ..., T_(m-1); i)`, with `n` leaves in total.
- The moves are pointer right/left and merge/split at the pointer.
- Every nonnegative `f` gives `||P|| >= <f, K f> / (4 <f, f>)`.

## 1. Bond-dimension-q ansatz (exact DP, float optimisation)

The ansatz is built from entrywise-positive `q x q` matrices, with trees of more than `N` leaves
given weight 0:

- `x(leaf) = X1` and `x((L,R)) = x(L) Φ(|L|,|R|) x(R)`;
- `y(leaf) = Y1` and `y((L,R)) = y(L) Γ(|L|,|R|) x(R)`;
- `f = u^T [Π_(j<i) x(T_j) R] y(T_i) R [Π_(j>i) x(T_j) R] v`.

When `q = 1` this is exactly the split-form ansatz.

Shape sums in `(q^2 x q^2)` Kronecker form turn `D_n` and `Num_n` into a matrix renewal. The DP in
`mps_forest.py` matches brute force to about `1e-16` for `q = 1, 2` and `n = 2..6` (`python
mps_forest.py test`). The stationary limit is `2 ℓHr / ℓQr`, and the finite-`n` values converge to it
like `1/n`.

The runs start from the `q = 1` optimum embedded as rank-one matrices, then use L-BFGS. The table
gives `R/4`. The `q = 2` runs were still climbing slowly when stopped at about 1350 s each. The stopped runs saved no
parameters, and each `.out` file records its final iterate.

| N | split optimum (q=1) | q = 2 (latest) |
|---|---|---|
| 9 | 0.87771 | 0.88183 |
| 20 | 0.91179 | 0.91737 |
| 40 | 0.92897 | 0.93292 |

For comparison, the split optimum at `N = 80` is 0.94002. So at every `N` tested, the gain from
`q = 2` correlations is smaller than the gain from roughly doubling the tree cap. There is no sign
that correlations lift the `N → ∞` iid ceiling of about 0.974 (the continuum functional).

## 2. The size-level relaxation (exact identity plus data processing)

**Exact identity.** For any `f >= 0`, set `π = f^2 / ||f||^2`. Then

    <f, K f> / (4 <f,f>) = [ BC(π, shift_* π) + BC(π, merge_* π) ] / 2 .

This holds because the reverse edges pair up; BC is the Bhattacharyya coefficient.

**Data processing.** Push `π` forward to the size sequence `(|T_j|)` seen from the pointer. This can
only increase each BC. Hence the quotient of every forest test vector is at most

    Σ_size := sup over laws on pointed integer sequences of [BC(ρ, σ_*ρ) + BC(ρ, m_*ρ)] / 2 .

Here `σ` moves the mark one gap to the right, and `m` adds the two gaps after the mark. This is a
marked point process on `Z` that is almost invariant under "move the mark to the next point" and
"delete the next point".

**Consequence (a new, separately fallible prerequisite).**

- Assume the forest-window quotients reach `||P||`. This is expected from `F = M M^(-1)`, because a
  finitely supported function right-translates into the positive monoid, but it is **not proved
  here**; it is the one gap.
- Under that assumption, F amenable implies `||P|| = 1`, which implies `Σ_size = 1`.
- Contrapositive: `Σ_size < 1` implies F is non-amenable.
- `Σ_size = 1` alone proves nothing, because the relaxation discards the split structure. Split is not
  determined by sizes, so this is not a Schreier graph.

**Stationary Markov size chains on `{1..K}`.** Here the shift term is 1, and

    BC_merge(P) = Σ μ(x) sqrt( P(x,y) P(y,z) · Σ_(a+b=y) P(x,a) P(a,b) P(b,z) ),

which is itself an upper bound (a 3-coordinate marginal). The table gives the maximised
`(1 + BC)/2` from `scan.out`.

| K | iid rows (P(x,·) = α) | Markov |
|---|---|---|
| 10 | 0.87439 | 0.87654 |
| 20 | 0.90393 | 0.90708 |
| 40 | 0.92212 | 0.92631 |
| 80 | 0.93396 | 0.93907 |

Both columns are still rising in `K`, so no ceiling below 1 is visible.

## Why sup = 1 at size level would be slow (heuristic, not proved)

Write `r_k = x_k / x_(k+1)`. A sawtooth sequence with typically huge ratios satisfies
`merge(r_(-1), r_0, r_1, r_2, ...) ≈ (r_(-1), r_0 r_1, r_2, ...)`. In the log-ratios, merge again
adds two consecutive gaps. The size-level problem therefore reproduces itself one logarithm down.
Descents must end at 1, and each up-jump costs an amount of order `margin / ln K`.

This suggests `1 − Σ_size(K)` decays only like an iterated-logarithm (log*) rate in `K`. If so,
`Σ_size = 1`, but no finite computation could separate it from a value below 1.

## Attempts

- **2026-09-19, swarm-0917-w14-w14-f-follow.** Bond-dimension-2 MPS test vectors and the size-level
  Markov scan, results as above.
  - *What stands:*
    - the matrix renewal DP (verified against brute force);
    - the exact BC identity;
    - the data-processing bound, and with it the prerequisite "F amenable implies `Σ_size = 1`".
  - *What is open:*
    - whether `Σ_size < 1`, which would prove non-amenability;
    - a proof of the regress heuristic, which would make the relaxation useless for non-amenability
      and explain the slow growth of forest test vectors.
  - *Where correlations die (numerically):* a bond dimension of 2 buys about the same as raising `N`
    by a factor of 1.3–2. No interval certificate was attempted.
