---
rg: 2
id: fpbs-tree-projected-oriented-second-moment-proof
kind: route
title: Paley–Zygmund over word-following decorated paths and the Ihara resolvent separate the thresholds
target: fpbs-tree-projected-oriented-second-moment-thresholds
requires:
  - fpbs-tree-projected-large-rank-strict-thresholds
artifacts:
  - experiments/tree-projected-second-moment-2026-09-17/criterion.py
  - experiments/tree-projected-second-moment-2026-09-17/output.txt
---

Notation as in the target. Write `G = Cay(Gamma,S)`, `A` for its adjacency operator,
`tau_p(x,y) = P_p(x <-> y)` and `T_p` for the operator with kernel `tau_p`. Let
`p_{2->2} = sup{p : ||T_p||_{2->2} < infinity}`. Put `x = 1/p`.

## 1. `p_c <= p_o`

**Subgraph.** Put `m = m_lo`. For each `t in B` choose `S'_t ⊆ S` with `|S'_t| = m` and
`pi(S'_t) = {t}`, and put `S'_(t^(-1)) = (S'_t)^(-1)`. Let `G'` be the subgraph with
edges `{g, gs}`, `s in S' = ∪ S'_t`. An infinite cluster of `G'` lies inside an
infinite cluster of `G`, so `p_c(G) <= p_c(G')`. We show that `G'` percolates for every
`p > p_o`.

**Word-following paths.** For `N >= 1` let `P_N` be the set of sequences
`(s_1, ..., s_N)` with `s_i in S'_(t_i)`, where `t_1 ... t_N` is a reduced word in
`B ∪ B^(-1)`. Map a sequence to the vertex path `g_0 = 1`, `g_i = g_(i-1) s_i`.
* `pi(g_i) = t_1 ... t_i` are distinct vertices of the tree, so the `g_i` are
  distinct. Every element of `P_N` is a self-avoiding path with `N` distinct edges.
* The number of reduced words is `W_N = 2n b^(N-1)`, so `|P_N| = W_N m^N`.
* Let `Z_N` be the number of open paths in `P_N`. Then `E Z_N = W_N (mp)^N`.

**Shared edges.** Take `γ, γ' in P_N` with words `t, t'`. Let `j` be the length of
their longest common prefix.
* The `i`-th edge of `γ` lies over the tree edge `(t_1...t_(i-1), t_1...t_i)`. So an
  edge of `γ` equals an edge of `γ'` only if it is the `i`-th edge of both paths with
  `i <= j`.
* The endpoints are then in the same fibres in the same order. So the edges agree iff
  `g_(i-1) = g'_(i-1)` and `s_i = s'_i`.
* Therefore `E[1_{γ open} 1_{γ' open}] = p^(2N) x^(σ)`, where `σ` counts such `i <= j`.

**Transfer bound.** Fix the common prefix `t_1...t_j`. Let `H_j` be the sum of `x^σ`
over all pairs `(s_1..s_j)`, `(s'_1..s'_j)` of decorations along it. At step `i`,
`g_(i-1)` and `g'_(i-1)` lie in one fibre `gH`, so `g'_(i-1) = g_(i-1) h` with `h in H`.
* *State 0, `h = 1`.*
  * `m` pairs have `s = s'`. The edge is shared (weight `x`) and the state stays 0.
  * `m(m-1)` pairs have `s ≠ s'`, so `gs ≠ gs'`. The state becomes nonzero.
* *Nonzero state, `h ≠ 1`.* The step returns to state 0 iff `s = h s'`. The number of
  such pairs is `|S'_t ∩ h S'_t|`. If this equalled `m`, then `h S'_t = S'_t`, and `h`
  would permute a finite set of group elements freely, so `h^(m!) = 1`. That is
  impossible in torsion-free `H`. So at most `m-1` pairs return and at least
  `m^2 - m + 1` stay nonzero. No edge is shared.

Put `T = [[m x, m^2 - m], [m - 1, m^2 - m + 1]]`, `u_0 = (1,1)` and `u_k = T u_(k-1)`.

*Claim:* the sum of `x^σ` over the remaining `k` steps is at most `u_k(0)` from
state 0 and at most `u_k(1)` from any nonzero state. Also `u_k(0) >= u_k(1)`. The
proof is by induction on `k`.
* From state 0 the sum is at most `m x u(0) + (m^2-m) u(1)` by the induction bounds.
* From a nonzero state it is at most `c u(0) + (m^2 - c) u(1)` with `c <= m-1`. Since
  `u(0) >= u(1)`, this is at most `(m-1) u(0) + (m^2-m+1) u(1)`.
* Finally, `u_k(0) - u_k(1) = (mx - m + 1) u(0) - u(1) >= m(x-1) u(0) >= 0`, since `x >= 1`.

So `H_j <= e_0 · T^j (1,1)`.

**Second moment.** Pairs of words with exact common prefix `j >= 1` number at most
`W_j b^(2(N-j))`. After the prefix, the decorations are free and share nothing, which
contributes `m^(2(N-j))`. Pairs with `j = 0` number at most `W_N^2` and share nothing.
Using `W_N = W_j b^(N-j)`,

```text
E Z_N^2 / (E Z_N)^2 <= 1 + sum_{j=1..N} H_j / (W_j m^(2j))
                    <= 1 + (b/2n) sum_{j>=1} e_0 · (T / (b m^2))^j (1,1).
```

This is bounded uniformly in `N` when `rho(T) < L := b m^2`. For a nonnegative
`2 x 2` matrix `[[α,β],[γ,δ]]`, `rho < L` iff `L > α`, `L > δ` and
`(L-α)(L-δ) > βγ`.
* Here `L > δ = m^2 - m + 1` because `b >= 3`.
* The last condition reads `(bm^2 - mx)((b-1)m^2 + m - 1) > m (m-1)^2`, that is,
  `x < b m - (m-1)^2/((b-1)m^2 + m - 1) = 1/p_o`. This also gives `L > α = mx`.

So for `p > p_o` there is `C < infinity` with `E Z_N^2 <= C (E Z_N)^2` for all `N`.

**Conclusion of step 1.**
* Paley–Zygmund gives `P(Z_N > 0) >= 1/C`.
* The events `{Z_N > 0}` decrease in `N`, since a prefix of an open path is open. So
  with probability at least `1/C` there are open self-avoiding paths from `1` of every
  length. The graph is locally finite, so König's lemma gives an infinite open path.
* Hence `p_c(G') <= p`. Letting `p ↓ p_o` gives `p_c(G) <= p_o`.
* For `m = 1` the matrix is `diag(x, 1)` and the condition is `p > 1/b`, the threshold
  of `T_(2n)`.

## 2. `p* <= p_{2->2} <= p_u`

**Norm.** `||A|| <= lam = v + 2 m_hi sqrt(b)` is step 2 of
`fpbs-tree-projected-large-rank-proof` (Schur blocks and Kesten), cited through
`fpbs-tree-projected-large-rank-strict-thresholds`.

**Non-backtracking walks.** `G` is `d`-regular. Let `B_k(x,y)` count non-backtracking
walks of length `k`. Then `B_0 = I`, `B_1 = A`, `B_2 = A^2 - dI` and
`B_(k+1) = A B_k - (d-1) B_(k-1)` for `k >= 2`, so `B_k = q_k(A)` for real polynomials
`q_k` with

```text
sum_k q_k(t) z^k = (1 - z^2) / (1 - t z + (d-1) z^2).
```

**Uniform analyticity.** Fix `p < p' < p*`, and let `|t| <= lam`. The roots of
`(d-1) z^2 - t z + 1` have product `1/(d-1)`.
* If `t^2 >= 4(d-1)`, both roots are real. The one of smaller modulus is
  `2/(|t| + sqrt(t^2 - 4(d-1)))`, which decreases in `|t|` and so is at least `p*`.
* Otherwise both roots have modulus `1/sqrt(d-1) >= p*`.

So the right-hand side is analytic on `|z| <= p'`. It is jointly continuous and hence
bounded by some `M` on `[-lam,lam] x {|z| <= p'}`. Cauchy's estimate gives
`sup_{|t| <= lam} |q_k(t)| <= M p'^(-k)`. The spectrum of `A` lies in `[-lam, lam]`, so
`||B_k|| <= M p'^(-k)` and `sum_k p^k ||B_k|| < infinity`.

**Comparison.**
* `tau_p(x,y)` is at most the sum of `p^k` over self-avoiding paths from `x` to `y`.
  Self-avoiding paths are non-backtracking walks. So entrywise
  `0 <= T_p <= K := sum_k p^k B_k`, a norm-convergent sum of nonnegative kernels.
* For nonnegative kernels the operator norm is monotone, so `||T_p|| <= ||K|| < infinity`.
* Hence `p* <= p_{2->2}`.

**Upper bound.** `p_{2->2} <= p_u` is step 4 of `fpbs-tree-projected-large-rank-proof`.
For `p > p_u`, Harris–FKG gives `tau_p >= theta(p)^2 > 0`, so `||T_p δ_1||_2 = infinity`.

## 3. Conclusion and corollary

If `p_o < p*`, then `p_c <= p_o < p* <= p_{2->2} <= p_u`.

**Corollary (uniform multiplicity `m >= 2`, `v <= 2`, `n >= 3`).**

*Setup.* Torsion-free `H` has no involutions, so vertical generators come in pairs
and `v in {0,2}`. Here `d - 1 = 2nm + v - 1` and `lam = v + 2m sqrt(b)`. The inequality
`lam^2 >= 4bm^2 > 4(d-1)` holds, so `p* = 2/(lam + sqrt(lam^2 - 4(d-1)))`.

*Reduction.* The inequality `sqrt(lam^2 - 4(d-1)) <= lam - 2(d-1)/lam` holds, because
squaring the right side adds `4(d-1)^2/lam^2`. Also `1/p_o > bm - 1/(b-1)`. So it
suffices that

```text
v + 2 sqrt(b) m - (d-1)/lam  <=  b m - 1/(b-1).                (*)
```

*Case `n >= 4`, so `b >= 7`.* Drop `(d-1)/lam`. The quantity `(b - 2 sqrt b) m` is
increasing in `b` and `m`, and at `b = 7`, `m = 2` it is `3.417 > 2 + 1/6`. So `(*)`
holds.

*Case `n = 3`, `m >= 3`.* `(d-1)/lam = (6m+v-1)/(2 sqrt5 m + v)` increases in `m`. At
`m = 3` it is at least `19/15.42 > 1.23`. Then `(*)` needs
`(5 - 2 sqrt 5) m >= v - 1.23 + 0.25`. That holds for all `m >= 3`, since the left side
is at least `1.58`.

*Case `n = 3`, `m = 2`.* `v = 2` gives `p_o = 1/(10 - 1/17) = 17/169`. `v = 0` gives the
same `p_o`. Both cases are checked exactly in `criterion.py` (`vmax = 2`).

The script re-verifies every case with `3 <= n <= 8`, `2 <= m <= 2000` and `v in {0,2}`
in exact rational arithmetic, using a rational upper bound for `sqrt(b)`.
