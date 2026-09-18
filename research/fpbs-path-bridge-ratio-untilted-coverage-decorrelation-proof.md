---
rg: 2
id: fpbs-path-bridge-ratio-untilted-coverage-decorrelation-proof
kind: route
title: Expanding r^N over covered subsets turns Br and the gap-split part of TJT into sums with the same weights, so Br/TJT is at most the untilted coverage ratio K; for two runs a last-exit union bound and FKG give K <= 2/theta
target: fpbs-path-bridge-ratio-untilted-coverage-decorrelation
requires:
  - fpbs-percolation-spine-path-bridge-ratio-criterion
---

Notation as in the target and in
`fpbs-percolation-spine-path-bridge-ratio-criterion`. The volume is a
chordless path `x_0 ... x_n` with edges `e_i = x_{i-1} x_i`, `r in (0,1)`,
`Z` is an environment independent of the labels, `N(i,j]` counts the edges
`e_{i+1},...,e_j` not in `Z`, and `t(i,j) = E r^{N(i,j]}`.

## 1. The subset expansion

For every configuration and every set `I` of path edges,

```text
r^{#(I \ Z)} = prod_{i in I} ( r + (1-r) 1{e_i in Z} ) = sum_{S ⊆ I} r^{|I|-|S|} (1-r)^{|S|} 1{S ⊆ Z}.
```

Write `w_I(S) = r^{|I|-|S|} (1-r)^{|S|}`. Taking expectations,
`E r^{#(I\Z)} = sum_{S ⊆ I} w_I(S) P(S ⊆ Z)`.

Fix `2 <= k <= n-1`, and let `I_k = Lambda \ {e_k}`, `I_k^- = {e_1..e_{k-1}}`,
`I_k^+ = {e_{k+1}..e_n}`. For `S ⊆ I_k` put `S^- = S ∩ I_k^-` and
`S^+ = S ∩ I_k^+`. Then `w_{I_k}(S) = w_{I_k^-}(S^-) w_{I_k^+}(S^+)`, and the
map `S -> (S^-, S^+)` is a bijection onto pairs of subsets. Hence

```text
t(0,k-1) t(k,n) = sum_{S ⊆ I_k} w_{I_k}(S) P(S^- ⊆ Z) P(S^+ ⊆ Z).      (1)
```

**Bridge mass.** By Theorem 1(a) of the criterion,
`Br(u,v) = E[G r^{N-1}] = sum_{k=2}^{n-1} E[ 1{e_k interior gap} r^{N-1} ]`.
On `{e_k notin Z}`, `N - 1 = #(I_k \ Z)`. So, by the expansion,

```text
Br(u,v) = sum_{k=2}^{n-1} sum_{S ⊆ I_k} w_{I_k}(S) P(S ⊆ Z, e_k interior gap)
        <= sum_{k=2}^{n-1} sum_{S ⊆ I_k} w_{I_k}(S) P(S ⊆ Z).                 (2)
```

**Two-point side.** Every term of `TJT(u,v) = sum_k [t(0,k-1)t(k,n) + t(0,k)t(k-1,n)]`
is nonnegative, so by (1)

```text
TJT(u,v) >= sum_{k=2}^{n-1} sum_{S ⊆ I_k} w_{I_k}(S) P(S^- ⊆ Z) P(S^+ ⊆ Z).   (3)
```

## 2. Theorem 1 (the mediant bound)

The sums (2) and (3) run over the same index set with the same weights.
If `P(S^- ⊆ Z) P(S^+ ⊆ Z) = 0` then `P(S ⊆ Z) = 0`, because
`{S ⊆ Z} ⊆ {S^- ⊆ Z}` and `{S ⊆ Z} ⊆ {S^+ ⊆ Z}`. So those terms vanish in
(2), and the mediant inequality `sum a_j / sum b_j <= max a_j/b_j` over the
terms with `b_j > 0` gives

```text
Br(u,v) / TJT(u,v) <= K_n(Z) = max_{2<=k<=n-1} max_{S ⊆ I_k, P(S⊆Z)>0} P(S ⊆ Z) / ( P(S^- ⊆ Z) P(S^+ ⊆ Z) ).
```

If `S^-` or `S^+` is empty the ratio is `1`. For positively associated `Z`
(for instance any increasing function of an i.i.d. field, by Harris-FKG) each
ratio is at least `1`.

For `D_n`: `D_n >= (1/n) sum_{k=2}^{n-1} t(0,k-1) t(k,n) / t(0,n)`. Also
`t(0,n) <= t(I_k)`, where `t(I_k) = E r^{#(I_k\Z)}`, since
`#(I_k \ Z) <= N`. The expansion of `t(I_k)` has the same weights as (1),
so `t(0,k-1) t(k,n) >= t(I_k) / K_n >= t(0,n) / K_n`, and

```text
D_n >= (1 - 2/n) / K_n(Z).
```

Both bounds hold for every environment and every `r`. The tilt `r^N`
enters only through the weights `w`, and these cancel. So the tilted
quasi-multiplicativity asked for in the criterion's next step is implied by
an untilted statement about the coverage events `{S ⊆ Z}` of the environment
alone, uniformly over the covered pattern `S`. ∎

## 3. Theorem 2 (two-run patterns)

Let `G` be any locally finite graph and `T ⊆ V` any vertex set (the
*target*). Let `omega` be Bernoulli(`p'`) bond percolation on `G`, and let
`Z` be the set of open edges with an endpoint joined to `T` by an open path.
If `T` is at infinity, meaning that the endpoint lies in an infinite cluster,
this is the percolation spine. A finite `T` (the boundary of a box) gives the
box proxies used in the computations. Put
`theta_min = min_{0<=i<=n} P(x_i <-> T)`.

For a set `F` of path edges, a *run* of `F` is a maximal set of consecutive
path edges in `F`. Put `P^F` for the law in which the edges of `F` are
declared open and every other edge is Bernoulli(`p'`), and

```text
q(F) = P^F( every run of F is joined to T ).
```

Given that `F` is open, `e in F` lies in `Z` iff its run is joined to `T`.
The run is connected, and it is contained in the open cluster of each of
its endpoints. The edges of `F` are independent of the others, so
`P(F ⊆ Z) = p'^{|F|} q(F)`.

**Claim.** Let `L, R` be runs (sets of consecutive path edges), with every
edge of `L` before every edge of `R`, and `L ∩ R = ∅`. Then

```text
q(L ∪ R) <= q(L) + q(R) <= (2/theta_min) q(L) q(R).
```

*Proof.* Let `F = L ∪ R`. Suppose every run of `F` is joined to `T` in
`omega ∪ F`. Pick an open path `pi` from `V(F)` to `T`. It is
simple, and if `T` is at infinity it is an infinite simple path. Let `y` be
the last vertex of `pi` in `V(F)`. Every edge of `pi` after `y` has at
most its first endpoint in `V(F)`, so none of these edges is in `F`. If
`y in V(L)`, then `y` is joined to `T` by edges of `omega` off `F`. This
event is measurable with respect to the edges off `F`. On it, the cluster of
`L` in the configuration "`L` open, all other edges as in `omega`" meets
`T`. The edges off `L` have the same law under `P^F` and under `P^L`,
except that `R` is open under `P^F`. The event does not use `R`. So its
`P^F`-probability is at most `q(L)`. The case `y in V(R)` gives at most
`q(R)`. Hence `q(L ∪ R) <= q(L) + q(R) <= 2 max(q(L), q(R))`.

For the second inequality: under `P^L` the run `L` is open, so
`{x ↔ T} ⊆ {L ↔ T}` for an endpoint `x` of `L`, and
`P^L(x ↔ T) >= P(x ↔ T) >= theta_min` because `P^L` dominates `P`. So
`min(q(L), q(R)) >= theta_min`, and
`max(q(L), q(R)) = q(L) q(R) / min(q(L), q(R)) <= q(L) q(R) / theta_min`. ∎

**Consequence for `K_n`.** Let `S ⊆ I_k` have at most one run on each side of
`e_k`. If one side is empty the ratio is `1 <= 2/theta_min`. Otherwise
`S^- = L`, `S^+ = R`, and the powers of `p'` cancel:

```text
P(S ⊆ Z) / (P(S^- ⊆ Z) P(S^+ ⊆ Z)) = q(L ∪ R) / (q(L) q(R)) <= 2/theta_min.
```

This includes the fully covered pattern `S = I_k`. For every `k` it gives the
one-arm quasi-multiplicativity of the attachment profile
`g(i,j) = q({e_{i+1},...,e_j})`:

```text
g(0,n) <= g(0,k) + g(k,n) <= (2/theta_min) g(0,k) g(k,n)          (0 < k < n),
```

by the same last-exit argument applied to `F = Lambda` split at the vertex
`x_k`. This is the inequality `g(n) <= C theta^{-1} g(k) g(n-k)` of the
criterion's next step, with `C = 2`, for every `k`, on every graph, at every
`p'` and for every target.

## 4. Corollary 3 (the small-`r` limit)

Fix `n`. As `r -> 0`, `w_{I_k}(S) -> 1{S = I_k}` for every `S ⊆ I_k`. Both
(2) and (3) are finite sums, so

```text
limsup_{r -> 0} Br/TJT <= sum_k P(I_k ⊆ Z) / sum_k P(I_k^- ⊆ Z) P(I_k^+ ⊆ Z) <= 2/theta_min,
liminf_{r -> 0} D_n >= (1 - 2/n) theta_min / 2 .
```

The bound is uniform in `n`, but the limit is taken at fixed `n`. It uses
only `I_k`, whose two sides are single runs. Here `Z` must not depend on
`r`. That is the case for the criterion's percolation spine at fixed `p'`.
∎

## 5. What is not proved

For a pattern `S` with several runs on one side of `e_k`, the last-exit
argument gives
`q(S) <= P^S(some run of S^- is joined to T off S, and every run is joined) + (same for S^+)`.
Here the runs of `S^-` may still be joined to `T` through the open edges of
`S^+`. So the argument does not factor, and the bound
`K_n <= C/theta_min` on multi-run patterns is left OPEN. It is exactly what
would make Theorem 1 give `Br/TJT <= C/theta` for all `r`.
