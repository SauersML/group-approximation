---
rg: 2
id: finite-scale-fixed-algebra-mass-transport-proof
kind: route
title: Proof that bijectivity of the compressor plus a scale hypothesis preserves Kazhdan fixed algebras, by mass transport of log cluster sizes
target: finite-scale-compressors-preserve-kazhdan-fixed-algebras
requires:
  - bounded-cluster-period-preserves-kazhdan-fixed-algebras
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
  - experiments/scale-mass-transport-2026-09-17/mt_check.py
---

The only prerequisite is item 1 (the loss bound) of the ESTABLISHED
`bounded-cluster-period-preserves-kazhdan-fixed-algebras`:
`sum_i ell_n(i) = o_U(|Y_n|)` for every cluster frame and every compressor. That item is
proved in `bounded-cluster-period-fixed-algebra-proof` from the frame and the relations
`u s u^-1 = w_s`, without Proposition 3.1.

Two statements are imported verbatim from `research/artifacts/kun-thom-2608-06222-verified.md`
(arXiv:2608.06222v1, the trust surface of `kun-thom-sofic-centralizer-normalization-citation`):

> [13, Theorem 1], as quoted on p. 4: "if H has property (T), then one can change
> o_𝒰(|Y_n|) edges so that the graphs become disjoint unions of graphs with a uniform
> positive Cheeger constant"

> Lemma 2.3: "D_𝒰^{σ(H)} = Π_{n→𝒰} D(𝒬_n)"

Lemma 2.3 is read, as in item 5 of the prerequisite, for the component partition of the
edited generator graph of the Kazhdan group `L`, which is the cluster frame. `D(Q_n)` is
the algebra of functions on `Y_n` constant on each cluster. Kun--Thom Proposition 3.1 is
**not** used.

Conventions. `o(·)` means `o_U(|Y_n|)`, and `n` is dropped where harmless. A permutation
`v` of `Y` acts on functions by `v · g = g ∘ v^-1`. So `Ad(v)` on multiplication operators
is `g -> g ∘ v^-1`, and `Ad(v) D(Q) = D(v Q)`, where `v Q = { v Q_i }`.

## Item 1: finite mass transport

Put `phibar = min(b, max(a, phi))`. This is monotone and `1`-Lipschitz in `phi`, with
values in `[a, b]`. Since `u` is a bijection of `Y`,
`sum_y phibar(u y) = sum_y phibar(y)`. Hence

```text
P := sum_y ( phibar(u y) - phibar(y) )_+  =  sum_y ( phibar(y) - phibar(u y) )_+ =: M.   (MT)
```

**Upper bound for `M`.**
- For `y ∉ E`, monotonicity and the Lipschitz bound give
  `phibar(u y) >= clamp(phi(y) - kappa(y)) >= phibar(y) - kappa(y)`. So the term of `y`
  in `M` is at most `kappa(y)`.
- For `y ∈ E`, the term is at most `b - a`.

So `M <= (b - a)|E| + sum_(y ∉ E) kappa(y)`.

**Lower bound for `P`.** Let `y ∉ E` with `a <= phi(y) <= b - eta` and
`phi(u y) >= phi(y) + eta`. Then:
- `phibar(y) = phi(y)`;
- `phi(u y) >= a`, so `phibar(u y) = min(b, phi(u y)) >= min(b, phi(y) + eta) = phi(y) + eta`.

So the term of `y` in `P` is at least `eta`. Now (MT) gives the inequality.

**The reversed form.** Apply the above to `-phi`, the window `[-b, -a]` and the same `E`
and `kappa`. The hypothesis becomes `phi(u y) <= phi(y) + kappa(y)`. The counted points
become those with `a + eta <= phi(y) <= b` and `phi(u y) <= phi(y) - eta`.

## Item 2: fixed-algebra invariance

Fix `theta = 1/8` and `eta = 1/8`. Then `(1 - theta) e^(-eta) > 0.77 > 1/2`.

**Step A: the bad set and the drift.** Call a cluster `Q_i` *good* if
`ell(i) <= theta |Q_i|`. Let `B` consist of the points of bad clusters, together with the
points `y` of good clusters `Q_i` with `u y ∉ Q_(pi i)`. Then

```text
|B|  <=  sum_(i bad) |Q_i|  +  sum_i ell(i)  <=  L/theta + L  =  9 L,    L = sum_i ell(i).
```

Let `y ∉ B` lie in `Q_i`. Then `u y ∈ Q_(pi i)` and
`|Q_(pi i)| >= |u Q_i ∩ Q_(pi i)| = |Q_i| - ell(i) >= (1 - theta)|Q_i|`. So

```text
phi(u y) >= phi(y) - kappa(y),     kappa(y) = -log(1 - ell(i)/|Q_i|) <= 2 ell(i)/|Q_i|,
```

using `-log(1 - x) <= x/(1 - x) <= 2x` for `0 <= x <= 1/2`. Summing over the points of
each cluster gives `sum_(y ∉ B) kappa(y) <= 2L`.

**Step B: upward jumps are negligible.** Let
`J = { y ∉ B : phi(u y) >= phi(y) + eta }`.
- Under `(LOG)`: `phi` takes values in `[0, log |Y|]`, and every `y ∈ J` has
  `phi(y) <= phi(u y) - eta <= log |Y| - eta`. Item 1 on the window `[0, log |Y|]` with
  `E = B` gives `eta |J| <= 9 L log |Y| + 2L`. So
  `|J|/|Y| <= (9 lambda_n log |Y_n| + 2 lambda_n)/eta`, whose `U`-limit is `0`.
- Under `(FS)`: given `eps`, take `k`, `Lambda` and intervals `I_r = [a_r, a_r + Lambda]`,
  `r <= k`, carrying `nu_n`-mass `>= 1 - eps`. Apply item 1 on the window
  `[a_r, a_r + Lambda + eta]`. It counts every `y ∈ J` with `phi(y) ∈ I_r`. So
  `eta |J ∩ phi^-1(I_r)| <= 9 (Lambda + eta) L + 2L`, and

  ```text
  |J|/|Y|  <=  eps  +  k (9 (Lambda + eta) + 2) lambda_n / eta.
  ```

  The `U`-limit is at most `eps`, for every `eps`.

In both cases `lim_U (|B_n| + |J_n|)/|Y_n| = 0`, since `lambda_n -> 0` by the loss bound.

**Step C: tight clusters have unique targets.** Call `Q_i` *tight* if it is good and
`|Q_(pi i)| < e^eta |Q_i|`. If `y ∉ B ∪ J` lies in `Q_i`, then
`phi(u y) = log |Q_(pi i)| < phi(y) + eta`, so `Q_i` is tight.

Suppose `i != i'` are tight with `pi i = pi i' = j`. The sets `u Q_i ∩ Q_j` and
`u Q_(i') ∩ Q_j` are disjoint, since `u` is injective. Each has size at least
`(1 - theta)|Q_i| > (1 - theta) e^(-eta) |Q_j| > |Q_j|/2`, which is impossible. So each `j`
has at most one tight preimage `tau(j)`.

**Step D: the approximant.** Let `g ∈ D(Q)`. Define `h ∈ D(Q)` on each `Q_j` as the value
of `g` on `Q_(tau(j))` when `tau(j)` exists, and as `0` otherwise. Let `y ∉ B ∪ J` lie in
`Q_i`, and let `j = pi i`, the cluster of `u y`. Then `Q_i` is tight, so `tau(j) = i` and
`h(u y) = g(y) = (g ∘ u^-1)(u y)`. So `g ∘ u^-1` and `h` agree off `u(B ∪ J)`, and

```text
|| g ∘ u^-1 - h ||_2^2 / |Y|  <=  4 ||g||_oo^2 (|B| + |J|) / |Y|.
```

The same bound holds for the normalized `1`-norm with `2 ||g||_oo` in place of
`4 ||g||_oo^2`.

**Step E: the ultraproduct.** Let `x ∈ D_U^(sigma(L))`. By Lemma 2.3,
`x = [g_n]` with `g_n ∈ D(Q_n)` and `sup_n ||g_n||_oo < infinity`. Then
`sigma(u) x sigma(u)^-1 = [g_n ∘ u_n^-1]`. By Steps B and D this equals `[h_n]`, whose
entries lie in `D(Q_n)`. So it lies in `prod_U D(Q_n) = D_U^(sigma(L))`, and

```text
Ad sigma(u) ( D_U^(sigma(L)) )  ⊆  D_U^(sigma(L)).
```

For the reverse inclusion:
- An element `x` commutes with `sigma(L)` if and only if `Ad sigma(u)(x)` commutes with
  `sigma(u) sigma(L) sigma(u)^-1 = sigma(u L u^-1)`. So
  `Ad sigma(u)(D_U^(sigma(L))) = D_U^(sigma(u L u^-1))`.
- `u L u^-1 <= L` gives `D_U^(sigma(L)) ⊆ D_U^(sigma(u L u^-1))`.

Hence

```text
D^(sigma L)  ⊆  D^(sigma(u L u^-1))  =  Ad sigma(u)(D^(sigma L))  ⊆  D^(sigma L),
```

and all three are equal. So `Ad sigma(u)` and `Ad sigma(u^-1)` map `D_U^(sigma(L))` onto
itself, and `sigma(L)` fixes it pointwise. Since `H = <L, u>`, every `sigma(g)` with
`g ∈ H` normalizes it.

(In Step D, `||h||_oo <= ||g||_oo`, so `[h_n]` is a bounded sequence.)

## Item 3: one-sided concentration

Put `psi(y) = log f(Q(y))`, `E = X_n` and `kappa(y) = log(1 + kappa_n) <= kappa_n`. Let
`y ∉ X_n` lie in `Q_i`. Then `i ∉ Bad_n` and `u y ∈ Q_(pi i)`, so
`psi(u y) = log f(pi i) <= psi(y) + kappa(y)`. Fix `c > 1`, put `eta = log c`, and let

```text
Dr_n = { y ∉ X_n : psi(u y) <= psi(y) - eta }.
```

- Under `(LOG_f)`: `psi` takes values in some `[m_n, m_n + R_n]`, and every `y ∈ Dr_n`
  has `psi(y) >= psi(u y) + eta >= m_n + eta`. The reversed form of item 1 on that window
  gives `eta |Dr_n| <= R_n |X_n| + kappa_n |Y_n| = o(·)`.
- Under `(FS_f)`: given `eps`, take intervals `I_r = [a_r, a_r + Lambda]`, `r <= k`, of
  mass `>= 1 - eps` for the distribution of `psi`. Apply the reversed form on the window
  `[a_r - eta, a_r + Lambda]`. It counts every `y ∈ Dr_n` with `psi(y) ∈ I_r`. So
  `|Dr_n| <= eps |Y_n| + k ((Lambda + eta)|X_n| + kappa_n |Y_n|)/eta`, whose `U`-limit
  over `|Y_n|` is at most `eps`.

Now let `i ∉ Bad_n` with `f(pi i) < f(i)/c`. Every point `y ∈ Q_i` either lies in `X_n`,
or satisfies `psi(u y) = log f(pi i) < psi(y) - eta`, and then `y ∈ Dr_n`. So the total
weight of these clusters is at most `(|X_n| + |Dr_n|)/|Y_n|`, with `U`-limit `0`. The
other side, `f(pi i) <= c f(i)`, holds off `Bad_n` as soon as `1 + kappa_n <= c`.

**Comparison with the Lean producer.** `MedianVertexForm.blockRatio_negligible`
(`GroupApproximation/KunThom/MedianVertexFormBlocks.lean`) has the hypotheses
- `hone`: `f n (pi q n i) <= (1 + kappa q n) f n i` for `i ∈ Dom`, `i ∉ Bad`;
- `hbad`, `hout`, `hmiss` and `huncov`: negligible weight of `Bad`, of the complement of
  `Dom`, of missing bridge mass, and of uncovered points.

Its conclusion is the two-sided ratio bound at `t` with `c = ((1 + 2 eta)/(1 - 2 eta))^2`.
Read `sourceDefect` of the bridge `i -> pi i` as the number of points of block `i` not
carried into block `pi i`, as its name and its role in `hmiss` indicate. This reading is
not checked against the Lean definitions. On it, the points not covered by these
hypotheses form a set `X_n` of the kind above, and the counting half of item 3 is that
conclusion at one compressor. Item 3 needs `(FS_f)` or
`(LOG_f)` for the observable where the Lean lemma uses `DG : ExpanderDecomposition A T`.

Item 3 is paper mathematics. It is not formalized, and it does not produce the other
fields of `CompressorRelativeData`. In the Lean files the ambient decomposition is also
read by `MedianVertexFormLocal.lean` and `Matching/GlobalVariation.lean`, through
`normalizedSize` of `Gamma`-blocks inside ambient blocks. Whether those uses can be
removed the same way is **not** checked here.

## Item 4: the doubling tower

Levels are `0 <= m <= k`, with `2^(k-m)` clusters of size `2^m` at level `m`. So each level
has mass `2^k`, and `|Y| = (k+1) 2^k`.
- For `m < k`, `u` maps the `c`-th pair of level-`m` clusters bijectively onto the `c`-th
  level-`(m+1)` cluster.
- `u` maps the top cluster bijectively onto the `2^k` singletons of level `0`.

This is a bijection of `Y`. Every cluster below the top has loss `0`. The top cluster has
loss `2^k - 1`, since its dominant target is a singleton. So:
- `lambda = (2^k - 1)/((k+1) 2^k) -> 0`;
- `lambda log |Y| = (1 - 2^-k)(k log 2 + log(k+1))/(k+1) -> log 2`;
- `nu` is uniform on `{0, log 2, ..., k log 2}`. Any `k'` intervals of length `Lambda`
  carry mass at most `k'(Lambda/log 2 + 1)/(k+1) -> 0`, so `(FS)` fails.

Every `u Q_i` is half of a cluster or a singleton, so `u Q` refines `Q` and
`D(Q) ⊆ D(u Q) = Ad(u) D(Q)`. Take `g ∈ D(Q)` with independent uniform signs on the
clusters.
- On a cluster `Q_j` above level `0`, `g ∘ u^-1` takes the signs of its two preimage
  clusters on the two halves.
- With probability `1/2` these differ. Then `sum_(Q_j) |g ∘ u^-1 - const| >= |Q_j|` for
  every constant in `[-1, 1]`.

So the expected `1`-distance from `D(Q)` is at least `|Y| k/(2(k+1))`, and some `g`
attains it. `mt_check.py` builds the tower for `k = 4, ..., 14`. It prints `lambda` from
`0.19` down to `0.067`, `lambda log |Y|` near `0.83`, `w(J_eta)` rising to `0.93`, and
normalized distance near `0.47`.

The tower is a finite combinatorial model. It carries no Kazhdan cluster structure, so it
is not a sofic representation of any `H`. It shows that the loss bound and bijectivity do
not by themselves give item 2. Whether such towers occur in sofic representations of
compressor groups of Kazhdan groups is the question left open (see below).

## Remarks

**Entropy form.** Put `H(Q) = sum_i (|Q_i|/|Y|) log(|Y|/|Q_i|) = log |Y| - E[phi]`. Since
`u` is a bijection, `u Q` has exactly the size profile of `Q`, so `H(u Q) = H(Q)`. Item 1 on
`[0, log |Y|]` is the statement that an approximate coarsening `u Q -> Q` preserving
entropy is an approximate isomorphism, with the continuity loss `O(lambda log |Y|)` that
entropy always carries. `(FS)` localizes the entropy count to finitely many scales, which
removes the `log |Y|`. Kun--Thom's ambient expander decomposition instead makes every
cluster observable almost `H`-invariant, with no scale at all.

**Numerical check.** `experiments/scale-mass-transport-2026-09-17/mt_check.py` checks:
- item 1 and the bounds of Steps A and D on 300 random multi-scale instances, with
  largest ratio `0.153` of the two sides of item 1;
- the tower of item 4;
- a single drifting cycle of `C` clusters of sizes in `[20, 40]`. For `C` up to `1280`,
  `BP_10` holds on mass `0`, `w(J_eta) = 0`, and the normalized distance of `Ad(u) g` from
  `D(Q)` is `0.0005`. This is the log-drift model of the prerequisite's remark, where no
  expander decomposition exists and item 2 still applies.
