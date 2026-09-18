---
rg: 2
id: fpbs-exhaustion-activation-gate-norm-law-proof
kind: route
title: Run the Bihari bound of the reduced gate in one exhaustion volume at a time, sandwich the spine-augmented norm between m^2|W| and B + B^2 m|W|, and chain the density windows of successive volumes
target: fpbs-exhaustion-activation-gate-norm-law
requires:
  - fpbs-spine-increment-activation-gate
  - fpbs-annealed-pivotal-factorization-off-spine-bridges
  - fpbs-volume-uniform-activation-gate-log-law
---

Notation as in the target. Norms are `l2 -> l2` on `W × W` matrices. For
nonnegative matrices `0 <= P <= Q` entrywise gives `||P|| <= ||Q||`, and a
compression of a nonnegative kernel has norm at most the kernel's norm.

## 1. Two norm bounds for one volume

Fix a finite edge set `Lambda`, `W = V(Lambda)`, `r in [t_0,t_1]`. Write
`X = X^Lambda_r`, `beta = beta^Lambda_r`, `S = S_r` compressed to `W`.

**Lemma 1.1 (upper bound).** `X <= beta + beta S beta` entrywise, hence
`||X|| <= B + B^2 sigma_r(W)`.

*Proof.* Condition on `M`. So `Z = Z_r` is frozen and `xi_r` is an
independent product measure. Let `u,v in W` and let `gamma` be a
self-avoiding path from `u` to `v` in `omega_r ∩ (Lambda ∪ Z)`. If `gamma` meets no
vertex of `V(Z)`, it uses no edge of `Z`. It is then a `xi_r`-open path in
`Lambda`. Otherwise let `x` be its first and `y` its last vertex in `V(Z)`. The
segment `gamma[u,x]` has no vertex of `V(Z)` before `x`, so it uses no
`Z`-edge. It is therefore a `xi_r`-open path in `Lambda`. Hence `x = u` or `x` is an
endpoint of a `Lambda`-edge; in both cases `x in W`. The same holds for
`gamma[y,v]`, and `y in W`. The two segments are vertex-disjoint except when
`x = y`, and edge-disjoint in every case. So the events
`{u <-> x in xi_r ∩ Lambda}` and `{y <-> v in xi_r ∩ Lambda}` occur disjointly.
By the union bound and the BK inequality for `xi_r`,

```text
P^M(u <-> v in omega_r ∩ (Lambda ∪ Z)) <= beta(u,v) + sum_{x,y in W} 1{x,y in V(Z)} beta(u,x) beta(y,v).
```

Here `beta` does not depend on `M`, because `U` is independent of `M`. Take
expectations: `X <= beta + beta S beta`. Finally,
`beta <= T^Bern_r <= T^Bern_{t_1}` entrywise, so `||beta|| <= B`. Also
`B >= 1`, by the unit diagonal. ∎

**Lemma 1.2 (lower bound).** `X >= S` entrywise on `W × W`, hence
`||X|| >= max(1, lambda_r(W))`.

*Proof.* By (E2), `Z` is connected, and `Z ⊆ omega_r ∩ (Lambda ∪ Z)`. So
`u, v in V(Z)` implies `u <-> v`. Then `||X|| >= <1_W, X 1_W>/|W| >= lambda_r(W)`,
and `||X|| >= 1` by the unit diagonal. ∎

**Lemma 1.3 (density bounds).** `m(r)^2 |W| <= lambda_r(W) <= sigma_r(W) <= m(r)|W|`.

*Proof.* By (E1), `P(x in V(Z_r)) = m(r)` for every `x`. So
`<1_W, S 1_W> = E[N^2]` with `N = |V(Z_r) ∩ W|`, and `E N = m(r)|W|`.
Cauchy–Schwarz gives `E[N^2] >= m(r)^2 |W|^2`. Next,
`lambda <= sigma` because `<1,S1>/|1|^2 <= ||S||`. Finally, `S` is symmetric
and nonnegative, so `||S||` is at most its maximal row sum. That row sum is
`sum_{y in W} P(x,y in V(Z_r)) <= m(r)|W|`. ∎

## 2. Theorem 1

Suppose the gate holds in `Lambda`, with an atomless finite measure
`kappa_A`. By Theorem 2 (R) of
`fpbs-annealed-pivotal-factorization-off-spine-bridges` (a connected
label-independent environment), `D^R_{s,t} <= 2(t-s) X_t J_W X_t`. Adding the
gate for `D^A` and using `X_t - X_s = D^R + D^A`:

```text
X_t - X_s <= kappa((s,t]) X_t J_W X_t,     kappa = 2 Leb + kappa_A  (finite, atomless).
```

`X_t` is nonnegative with unit diagonal and nondecreasing in `t`. Theorem 1 of
`fpbs-spine-increment-activation-gate` gives
`1/||X_s|| - 1/||X_t|| <= d kappa((s,t])`. It is applied here to this one
volume: its proof uses only the matrices of one `W`. Insert Lemma 1.1 at `s`
and Lemma 1.2 at `t`. Lemma 1.3 is proved above. ∎

## 3. Theorem 2

If `m(s) <= 1/|W|`, then `sigma_s(W) <= 1` by Lemma 1.3, so
`||X_s|| <= B + B^2`. If `m(t) >= sqrt(A/|W|)`, then
`lambda_t(W) >= m(t)^2 |W| >= A`, so `||X_t|| >= A = 2(B+B^2)`. Theorem 1 gives

```text
d (kappa_A((s,t]) + 2(t-s)) >= 1/(B+B^2) - 1/(2(B+B^2)) = 1/(2(B+B^2)) .   ∎
```

**Windows in `r`.** For finite `W` with `|W| > A` and `sqrt(A/|W|) <= m(t_1)`,
put

```text
s_W = max{ r : m(r) <= 1/|W| },       t_W = min{ r : m(r) >= sqrt(A/|W|) }.
```

Both exist by (E3) and monotonicity of `m`. They satisfy `m(s_W) = 1/|W|`,
`m(t_W) = sqrt(A/|W|)` and `s_W < t_W`, since `1/|W| < sqrt(A/|W|)`. Theorem 2
applies to `(s_W, t_W]`. If the top value of one window is at most the
bottom value of another, the two `r`-intervals are disjoint: if
`sqrt(A/|W|) <= 1/|W'|`, then `t_W <= s_{W'}`,
because `t_W` is the least `r` with `m(r) >= sqrt(A/|W|)` and
`m(s_{W'}) = 1/|W'| >= sqrt(A/|W|)`.

## 4. Corollary 3

`m(t_0) = 0` and `m(t_1) > 0`. By continuity `s* = max{r : m(r) = 0}` exists
and `s* < t_1`. Fix `t in (s*, t_1]`, so `m(t) > 0`, and suppose (AG) holds
along `(Lambda_j)` with a finite atomless `kappa_A`. Then `|W_j| -> infinity`,
because `G` is infinite and the `Lambda_j` exhaust `E`.

Choose indices `j_1 < j_2 < ...` with `|W_{j_1}| > A`,
`sqrt(A/|W_{j_1}|) <= m(t)` and `|W_{j_{n+1}}| >= A |W_{j_n}|^2`. Then
`sqrt(A/|W_{j_{n+1}}|) <= 1/|W_{j_n}|`, so by Section 3 the intervals
`I_n = (s_{W_{j_n}}, t_{W_{j_n}}]` are pairwise disjoint. They lie in
`(s*, t]`: `m > 0` on them, and `m(t_{W_{j_n}}) <= m(t)`. By Theorem 2,
`kappa_A(I_n) >= c_0 - 2|I_n|`. The `I_n` are disjoint in `[t_0,t_1]`, so
`sum_n |I_n| <= t_1 - t_0`, hence `|I_n| -> 0`. So
`kappa_A((s*,t]) >= sum_n kappa_A(I_n) = infinity`, a contradiction.

For (AG*): Theorem 2 (A) there gives `D^A <= beta (S_t - S_s) beta`, so (AG*)
implies (AG). For the full gate `X_t - X_s <= kappa((s,t]) X_t J X_t`, apply
Theorem 1 of `fpbs-spine-increment-activation-gate` directly with `kappa` in place of
`2 Leb + kappa_A`. The same argument then runs with `c_0` and without the
`2(t-s)` term. ∎

## 5. Theorem 4

**Generic (log-log) law.** Let `|W_{j+1}| <= D|W_j|`, `a = AD`, and let
`s < t` with `m(t) <= 1/|W_1|`. We may assume `m(s) > 0`; otherwise replace `s`
by any point of `(s*, t)` and let it decrease to `s*`. Put `ell_0 = m(s)` and
`ell_{k+1} = sqrt(a ell_k)`. Then `z_k = log(a/ell_k)` satisfies
`z_{k+1} = z_k/2`, and `z_0 = log(a/m(s))`. Let
`N = floor(log_2(log(a/m(s))/log(a/m(t))))`. Then `z_N >= log(a/m(t))`, that is,
`ell_N <= m(t)`. The `ell_k` increase because `ell_k < a`.

For `k < N` let `j(k)` be the largest `j` with `|W_j| <= 1/ell_k`. It exists
because `ell_k <= m(t) <= 1/|W_1|`. Maximality gives `|W_{j(k)+1}| > 1/ell_k`,
and hence `|W_{j(k)}| > 1/(D ell_k)`. So the window of `W_{j(k)}` satisfies

```text
bottom = 1/|W_{j(k)}| >= ell_k ,        top = sqrt(A/|W_{j(k)}|) < sqrt(A D ell_k) = ell_{k+1} <= m(t).
```

If `|W_{j(k)}| <= A`, the top value exceeds `1`, which is impossible since it
is `< ell_{k+1} <= 1`. So `|W_{j(k)}| > A`, and Section 3 applies. The windows
for `k = 0, ..., N-1` lie in `[m(s), m(t)]`. Each top is below the next
bottom, so the `r`-intervals are disjoint and contained in `(s,t]`. Summing
Theorem 2 over them, the `2|I|` terms add up to at most `2(t-s)`:

```text
kappa_A((s,t]) >= c_0 N - 2(t-s).
```

**Decorrelated (log) law.** Assume (Dec). The maximal row sum of `S_r` on `W`
is `sum_{y in W} P(x,y in V(Z_r))`. Split it into `y` with `d(x,y) <= L`, at
most `|B_L|` terms, each `<= m`, and the remaining `y`, each
`<= C_D m^2`. This gives

```text
sigma_r(W) <= m(r) |B_L| + C_D m(r)^2 |W| .
```

Hence `sigma_s(W) <= 1` whenever `m(s) <= 1/(2|B_L|)` and
`m(s) <= 1/sqrt(2 C_D |W|)`. The proof of Theorem 2 then gives
`kappa_A((s,t]) >= c_0 - 2(t-s)` whenever, in addition,
`m(t) >= sqrt(A/|W|)`. The window of `W` is now
`[1/sqrt(2 C_D |W|), sqrt(A/|W|)]`, with fixed ratio `sqrt(2 A C_D)`, and it
lies below `1/(2|B_L|)` by the hypothesis `m(t) <= 1/(2|B_L|)`.

Chain with `ell_{k+1} = K ell_k`, `K = sqrt(2 A C_D D)`. Given `ell_k <= m(t)`,
let `j(k)` be the largest `j` with `1/sqrt(2 C_D |W_j|) >= ell_k`, that is,
`|W_j| <= 1/(2 C_D ell_k^2)`. It exists because `ell_k <= 1/sqrt(2 C_D |W_1|)`.
Maximality gives `|W_{j(k)}| > 1/(2 C_D D ell_k^2)`, so the top of its window
is `< sqrt(2 A C_D D) ell_k = ell_{k+1}`. With
`N = floor(log(m(t)/m(s))/log K)` we have `ell_N <= m(t)`. The `N` windows are
disjoint in `(s,t]`, and summing gives
`kappa_A((s,t]) >= c_0 N - 2(t-s)`. Each window needs `|W| > A`, which holds
here as in the generic case, since its top value is below `1`.

**Arbitrary exhaustion.** Without a growth ratio, the same summation gives
`kappa_A((s,t]) >= c_0 N' - 2(t-s)`. Here `N'` is the largest number of volumes whose
windows lie in `[m(s), m(t)]` with each top below the next bottom. ∎

## 6. Remarks

* **Where the two-edge argument went.** The volume-uniform law used volumes in
  which `u` and `v` are Bernoulli-disconnected. An exhaustion volume is
  eventually connected, so its entries cannot be tested that way. The norm
  replaces the entries. Theorem 1 of the reduced gate turns a norm increase
  from `O(1)` to `>= A` inside one volume into a fixed mass. The spine alone
  forces that increase, through `||X|| >= m^2 |W|`, while
  `||X|| <= B + B^2 m |W|` keeps the norm bounded before the window.
* **Why the rate is log-log in general.** The factor between the lower bound
  `m^2|W|` and the upper bound `m|W|` is `m`. Without decorrelation, a window
  must run from `1/|W|` to `|W|^{-1/2}`, which squares the density scale per
  step. Under (Dec) both bounds are of order `m^2|W|`. The window then has
  bounded ratio, as in the two-edge law.
* **Hypothesis (H_B) is used once**, in Lemma 1.1, to keep `||beta^Lambda_s||`
  bounded uniformly in the volume. On an amenable graph `p_{2->2} = p_c`, so
  (H_B) fails at `t_0 = p_c`. There the Bernoulli norm itself carries the growth.
