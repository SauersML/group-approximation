---
rg: 2
id: fpbs-product-fibre-bounded-width-branching-fails
kind: claim
title: On products with a high-degree factor, fibre branching that keeps boundedly many child clusters per fibre has vanishing mean, and the factor susceptibility lives in clusters of size order 1/p^2
distinct_from:
  fpbs-product-fibre-collision-loss-vanishes: that is the open inequality on the collision loss L_p; this proves that every lower bound for the fibre branching which contracts a child fibre to boundedly many clusters fails, and locates the mass of chi in clusters of size of order 1/p^2, so L_p must be controlled on landing sets of divergent size
  fpbs-fibre-renormalized-nonbacktracking-certificate: that proves the certificate and Theorem B used here; this is a consequence about which explorations can realise its branching
artifacts:
  - experiments/fibre-bounded-width-2026-09-17/landing_width.py
---

**ESTABLISHED.** Self-contained proof below. Inputs: Theorem B of
`fpbs-fibre-renormalized-nonbacktracking-certificate` (ESTABLISHED), the
hitting-time theorem for Galton--Watson trees, and Robbins' Stirling bounds.

**Setting.** `(B,S_B)` is any infinite group with a finite symmetric generating
set of size `D = |S_B| >= 3`, and `m = D - 1`. Write `C` for the open cluster of `o`
in `Cay(B,S_B)` under Bernoulli(`p`) bond percolation, and `chi = E_p|C|`.
`G = Cay(H,S_H) □ Cay(B,S_B)` with `d_H = |S_H|`.

**Theorem 1 (tail).** For every `p <= 1/m` and every `n >= 1`,
`P_p(|C| >= n) <= 12 n^{-1/2}`.

**Corollary 2 (landing sets are usually empty).** For `p <= 1/m`,

```text
W(p) := E_p[min(1, p|C|)] <= 24 sqrt(p).
```

For `s ∈ S_H` the landing set `{(hs,z) : z ∈ C, edge (h,z)(hs,z) open}` of
the `s`-edges out of the fibre cluster of `(h,o)` is nonempty with
probability `E[1-(1-p)^{|C|}] <= W(p)`.

**Corollary 3 (mass of chi).** For `p <= 1/m` and every `K >= 1`,
`sum_{n <= K} n P_p(|C| = n) <= 24 sqrt(K)`. If also
`p ∈ (p_c(G), p_c(B))`, then `chi >= (1+p)/(p d_H)`, so the share of `chi`
carried by clusters with `|C| <= K` is at most `24 d_H p sqrt(K)`, and it tends
to `0` whenever `K = o(1/p^2)`.

**Corollary 4 (class kill).** Call a fibre exploration of `G` *of width `M`*
if, for each explored fibre cluster and each `s ∈ S_H`, it keeps at most `M`
fibre clusters of the child fibre `hsB` as offspring, all hit by the landing
set. Its mean offspring is at most `M d_H W(p) <= 24 M d_H sqrt(p)`. So for
`p <= 1/m` with `24 M d_H sqrt(p) < 1` it is a subcritical process and proves
nothing. This holds uniformly on the whole range `p <= 1/(D-1)`. For `Z^k` that
range misses only a window of width `O(k^{-3})` below `p_c(Z^k)` (see below).

- *Invariant:* bounded width, meaning the child fibre is contracted to
  boundedly many clusters.
- *Where every member dies:* at the mean-offspring step. The BK branching of
  Theorem B has mean `d_H p chi >= 1 + p`, but a fraction at least
  `1 - 24 M d_H sqrt(p)` of it comes from rare fibre clusters whose landing
  sets contain many points.

## Proof

**Step 1: domination.** Explore `C` from `o`. The root has at most `D`
unexplored edges, and every later vertex has at most `m` edges not yet
examined, since it was reached along one edge. Hence `|C|` is stochastically
dominated by the total progeny of a Galton--Watson tree with root offspring
`Bin(D,p)` and later offspring `Bin(m,p)`. For `p <= 1/m`, `Bin(m,p)` is
dominated by `Bin(m,1/m)`, and `Bin(D,p) = Bin(m,p) + Ber(p)`. So
`|C| <=_st T_1 + T_2`, where `T_1, T_2` are independent copies of the total
progeny `T` of the critical tree with offspring law `Bin(m,1/m)` started from
one individual.

**Step 2: hitting-time theorem.** For a Galton--Watson tree from one individual
with iid offspring `X_i`, `P(T = n) = (1/n) P(X_1+...+X_n = n-1)` (Otter--Dwass;
van der Hofstad, *Random Graphs and Complex Networks* Vol. 1, Theorem 3.14).
Here `X_1+...+X_n ~ Bin(nm, 1/m)`.

**Step 3: binomial point bound.** By Robbins' bounds
`sqrt(2 pi N)(N/e)^N <= N! <= sqrt(2 pi N)(N/e)^N e^{1/(12N)}`, for `0<j<N`,

```text
binom(N,j) q^j (1-q)^(N-j) <= e^{1/12} sqrt(N/(2 pi j (N-j))) exp(-N KL(j/N || q)),
```

and `KL >= 0`. Take `N = nm`, `j = n-1` and `n >= 2`. Then
`j(N-j)/N = (n-1)(nm-n+1)/(nm) >= (n-1)(m-1)/m >= (n-1)/2`, because `m >= 2`. So
`P(T = n) <= e^{1/12} pi^{-1/2} n^{-1} (n-1)^{-1/2} <= 0.62 (n-1)^{-3/2}`.

**Step 4: tail.** For `n >= 3`, comparing with `int_{n-2}^inf x^{-3/2} dx`,
`P(T >= n) <= 0.62 sum_{j>=n} (j-1)^{-3/2} <= 1.24 (n-2)^{-1/2} <= 4 n^{-1/2}`.
The last step is `1.24^2 n <= 16(n-2)`, which holds for `n >= 3`. For `n <= 2`,
the bound `4 n^{-1/2} >= 2.8` is trivial. Since `T` is integer-valued,
`P(T >= x) <= 4 x^{-1/2}` for all real `x > 0`. Therefore
`P(|C| >= n) <= P(T_1 >= n/2) + P(T_2 >= n/2) <= 8 (n/2)^{-1/2} < 12 n^{-1/2}`.
This proves Theorem 1.

**Step 5: Corollary 2.** `E[min(1,p|C|)] = int_0^1 P(|C| > s/p) ds <= int_0^1 12 (p/s)^{1/2} ds = 24 sqrt(p)`,
and `1-(1-p)^n <= min(1,pn)`. The `s`-edges out of the fibre are independent
of the fibre edges, so given `C` the landing set is nonempty with conditional
probability `1-(1-p)^{|C|}`.

**Step 6: Corollary 3.** `sum_{n<=K} n P(|C|=n) <= sum_{n=1}^K P(|C|>=n) <= 12 sum_{n<=K} n^{-1/2} <= 24 sqrt(K)`.
Suppose `p ∈ (p_c(G), p_c(B))`. Then `chi < infinity`, by sharpness of the
phase transition on the transitive graph `Cay(B,S_B)` (Aizenman--Barsky,
Menshikov). Apply Theorem B with `N = B`, `S_N = S_B` and `S' = S_H`, so that
`d' = d_H`. Since `p > p_c(G)`, its hypothesis fails, so `p(d_H chi - 1) >= 1`.

**Step 7: Corollary 4.** An individual contributes at most `M` offspring in
child fibre `hsB`, and only if the `s`-landing set is nonempty. Summing over
`s ∈ S_H` gives mean `<= M d_H W(p)`. QED.

## Calibration (B = Z^k, H = F_2)

`experiments/fibre-bounded-width-2026-09-17/landing_width.py` computes the exact
dominating Galton--Watson law at `p = 1/(2k + ||A_H|| + 1.1)`, which is below
`1/(2k-1)` and near the heuristic `p_c(G_k)`. Results:

* `sqrt(k) W` rises `0.53, 0.71, 0.87, 0.97, 1.04, 1.07` for
  `k = 10, 30, 100, 300, 1000, 3000`.
* `p E[T]` stays at about `0.18 ≈ 1/(||A_H||+2)`.
* The share of `E[T]` carried by `T > 2k` rises `0.31, 0.52, 0.71, 0.83, 0.90, 0.94`.

So the constant `24` in Corollary 2 is loose, but the order `k^{-1/2}` is sharp.

## What this changes

* The node's picture of fibre clusters "contracted to their susceptibility" is
  misleading in the only regime it targets. Almost all of `chi` sits in
  clusters of size about `1/p^2 ≍ d_k^2`, which put about `1/p ≍ d_k` landing
  points into each child fibre. Any rigorous version of the inequality
  `L_p -> 0` has to show that these many landing points reach mostly distinct
  child clusters. That is a many-point connectivity estimate inside `B_k`
  (a triangle-type sum over pairs of landing points), not a
  one-cluster-per-fibre branching bound.
* Width-`M` renormalisations are dead for every `M` fixed as `k -> infinity`.
  This includes multi-type Galton--Watson lower bounds whose type is the
  number of hit clusters truncated at `M`.
* **Not covered:** `p ∈ (1/(D-1), p_c(B))`, where the domination by a critical
  tree fails. For `Z^k` this window has width `O(k^{-3})` in the vdHS
  expansion. A mean-field tail `P_{p_c}(|C| >= n) <= C n^{-1/2}`, with `C` uniform
  in `k`, would close it. That bound is not imported here.
