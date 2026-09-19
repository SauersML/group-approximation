---
rg: 2
id: fpbs-half-space-first-entry-renewal-dies-at-level-reach-proof
kind: route
title: BK at the first entry into a half-space, iterated k times, bounds the level-reach probability by G(J)^k, so the level-reach lemma forces every half-space coefficient up to 1, and the only Holder closing left needs a slab l^q bound that already forbids uniqueness
target: fpbs-half-space-first-entry-renewal-dies-at-level-reach
requires:
  - fpbs-no-infinite-cluster-bounded-in-height
---

**Notation.** As in the target. `P = P_p` with `p > p_c(G)`, so that
`theta = theta(p) > 0`. The group acts by left multiplication and preserves
`P` and height differences. Hence:
- `P(y in FE_n(x)) = P(x^(-1) y in FE_n(o))`;
- `tau_p(x,y) = tau_p(o, x^(-1) y)`.

**Two facts about first entries.**
- **(F1)** Let `x` be a vertex and `n >= 1`. If `z in FE_n(x)`, then
  `h(x) + n <= h(z) <= h(x) + n + K - 1`. The reason is that the vertex before
  `z` on a witnessing path has height `< h(x) + n`, and one edge changes `h` by
  at most `K`.
- **(F2)** Let `gamma` be an open path from `x`, and let `y` be the first
  vertex of `gamma` with `h(y) >= h(x) + n`. Then `y in FE_n(x)`, witnessed by
  the initial segment of `gamma` up to `y`. Here `x` itself qualifies as a
  non-final vertex, since `h(x) < h(x) + n`.

Witnessing paths can always be taken simple. Loop-erasing a witness keeps its
vertex set inside the original one, and keeps its endpoints. So distinct
segments of one simple path use disjoint edge sets. This is what makes the
events below occur disjointly, in the sense of BK.

## Item 1: the renewal

**The first-entry inequality.** Let `n >= 1`, `m >= K`, and
`z in FE_(n+m)(o)`, witnessed by a simple open path `gamma`.
- Since `h(z) >= n + m >= n`, the path enters `U_n`. Let `y` be its first
  vertex in `U_n`. By (F2), `y in FE_n(o)`.
- By (F1), `n <= h(y) <= n + K - 1 < n + m`. So `y != z`.
- Put `m' = n + m - h(y)`. Then `m - K < m' <= m`, and `m' >= 1` since
  `m >= K`.
- Every vertex of the segment `gamma[y,z]` except `z` is a non-final vertex
  of `gamma`, so it has height `< n + m = h(y) + m'`. Hence
  `z in FE_(m')(y)`.

The two segments are edge-disjoint, so

```text
{z in FE_(n+m)(o)}  ⊂  ∪_(y : n <= h(y) < n+K)  {y in FE_n(o)} ∘ {z in FE_(n+m-h(y))(y)}.
```

Both events are increasing. The union bound and BK give

```text
P(z in FE_(n+m)(o)) <= sum_y P(y in FE_n(o)) P(z in FE_(n+m-h(y))(y)).
```

Multiply by `e^(mu h(z)) = e^(mu h(y)) e^(mu (h(z)-h(y)))` and sum over `z`.
By translation invariance,

```text
sum_z P(z in FE_(m')(y)) e^(mu (h(z)-h(y))) = G_mu(m').
```

Hence

```text
G_mu(n+m) <= sum_y P(y in FE_n(o)) e^(mu h(y)) G_mu(n+m-h(y)) <= G_mu(n) max_(m-K < m' <= m) G_mu(m').
```

All terms are nonnegative, so the convention `0 * infinity = 0` is harmless.

For a submultiplicative weight, `w(z) <= w(y) w(y^(-1) z)`. The same
computation, with `G_w(m') = E sum_(z in FE_(m')(o)) w(z)`, gives the same
inequality.

**The pointwise chain.** Fix `J >= K`, and `x`, `z` with
`H = h(z) - h(x) >= 0`. Suppose `x <-> z`, and let `gamma` be a simple open
path from `x` to `z`. Define the chain as follows.
- `y_0 = x`.
- While `h(z) - h(y_i) >= J`, let `y_(i+1)` be the first vertex of `gamma`
  after `y_i` with `h >= h(y_i) + J`. It exists, because `z` qualifies.
- By (F2) applied to `gamma[y_i, z]`, `y_(i+1) in FE_J(y_i)`.
- By (F1), `J <= h(y_(i+1)) - h(y_i) <= J + K - 1`.

Let `k` be the index where the chain stops, so `h(z) - h(y_k) < J`.
- If `k = 0`, then `h(z) - h(y_k) = H >= 0`.
- If `k >= 1`, then `h(z) - h(y_k) >= h(z) - h(y_(k-1)) - (J+K-1) >= -(K-1)`.

In both cases `-K < h(z) - h(y_k) < J`. The segment `gamma[y_k, z]` is open,
so the final factor is an event of probability `T^J(y_k, z)`. Since
`h(y_k) - h(x) <= k(J+K-1)` and `h(z) - h(y_k) < J`, we get
`k > (H-J)/(J+K-1) >= (H-J)/(J+K)`.

The `k+1` segments of `gamma` are edge-disjoint. Hence

```text
{x <-> z}  ⊂  ∪_(k >= (H-J)/(J+K))  ∪_(y_1..y_k)  {y_1 in FE_J(x)} ∘ ... ∘ {y_k in FE_J(y_(k-1))} ∘ {y_k <-> z},
```

where the last factor is taken only for `-K < h(z) - h(y_k) < J`. BK for
`k+1` increasing events, applied inductively, and the union bound give

```text
tau_p(x,z) <= sum_(k >= (H-J)/(J+K)) (Q_J^k T^J)(x,z).
```

This proves item 1.

## Item 2: the level-reach floor

Let `n >= 1`. On `{o <-> U_n}`, take an open path from `o` into `U_n`. Since
`h(o) = 0 < n`, (F2) says its first vertex in `U_n` lies in `FE_n(o)`. So
`|FE_n(o)| >= 1` on this event, and

```text
G(n) >= P(o <-> U_n) >= theta(p),
```

where the second inequality is the corollary of
`fpbs-no-infinite-cluster-bounded-in-height`.

For the tilt, (F1) gives `h(z) in [n, n+K-1]` on `FE_n(o)`. So
`e^(mu h(z)) >= e^(mu n) min(1, e^(mu(K-1)))`, and

```text
G_mu(n) >= P(FE_n(o) != ∅) e^(mu n) min(1, e^(mu(K-1))) >= theta e^(mu n) min(1, e^(mu(K-1))).
```

## Item 3: half-space percolation gives infinity

Let `n >= 1`. Suppose that, with positive probability, `o` lies in an
infinite component `D` of the open subgraph induced on `L_n`. Note that
`o in L_n`. By item 3 of `fpbs-no-infinite-cluster-bounded-in-height`,
almost surely on this event `D` has infinitely many open edges `{u,v}` with
`u in D` and `v in U_n`.

For each such edge, take an open path from `o` to `u` inside `D`, and append
the edge. Every vertex except `v` lies in `L_n`, so `v in FE_n(o)`. The graph
has bounded degree, so infinitely many edges have infinitely many distinct
endpoints `v`. Hence `|FE_n(o)| = infinity` with positive probability, and
`G(n) = infinity`.

## Item 4: the scalar kill

Fix `J >= 1` and `k >= 1`. Let `N >= (k-1)(J+K-1) + J`.

On `{o <-> U_N}`, let `gamma` be a simple open path from `o` to its first
vertex `z` in `U_N`. Run the chain of item 1 with step `J` along `gamma`,
stopping only when `h(z) - h(y_i) < J`.

By (F1), `h(y_i) <= i(J+K-1)`. So for `i <= k-1`,

```text
h(z) - h(y_i) >= N - (k-1)(J+K-1) >= J,
```

and the chain makes at least `k` steps. The segments are edge-disjoint, and
`y_i in FE_J(y_(i-1))` for `i <= k`. Hence

```text
{o <-> U_N}  ⊂  ∪_(y_1..y_k)  {y_1 in FE_J(o)} ∘ {y_2 in FE_J(y_1)} ∘ ... ∘ {y_k in FE_J(y_(k-1))}.
```

Weight the bound by `e^(mu h(y_k))` and use (F1) again. BK, the union bound
and translation invariance give

```text
theta(p) <= P(o <-> U_N) <= sum_(y_1..y_k) prod_(i=1..k) Q_J(y_(i-1),y_i) = G(J)^k.
```

To see this, sum over `y_k` first, then `y_(k-1)`, and so on. Each sum is
`sum_y Q_J(x,y) = G(J)`. The first inequality is item 2.

This holds for every `k`, so `G(J) >= theta^(1/k) -> 1`. Hence `G(J) >= 1`.

**Tilts.** On the event above, `h(y_k) in [kJ, k(J+K-1)]`, by (F1). So
`e^(mu h(y_k)) >= e^(mu k J) min(1, e^(mu k (K-1)))`. Inserting this weight,
which equals `prod_i e^(mu (h(y_i) - h(y_(i-1))))`, gives

```text
theta(p) e^(mu k J) min(1, e^(mu k (K-1))) <= G_mu(J)^k.
```

Take `k`-th roots and let `k -> infinity`. This gives

```text
G_mu(J) >= e^(mu J) min(1, e^(mu(K-1))).
```

For a weight `w >= 1`, `G_w(J) >= G(J) >= 1`. The window bounds follow by
taking the maximum.

**Why this is the closing condition.**
- The scalar renewal of item 1 closes only through a coefficient `< 1`.
  Either `M = max_(m-K < m' <= m) G(m') < 1`, which iterates to
  `G(km) <= M^k` and so to decay of `G` and of `tau_p` in height, or
  `G(J) < 1` in the chain. Both are excluded.
- For a tilt, the iteration gives `G_mu(km) <= M_mu^k`. This converts into
  decay of `G(km)` only if `M_mu < e^(mu m)` up to the constant
  `min(1, e^(mu(K-1)))`, since `G(km) <= e^(-mu km) max(1, e^(-mu(K-1))) G_mu(km)`.
  That is excluded too.
- For `mu < 0`, a bound `M_mu < 1` is consistent with the floor. It gives only
  `G(km) <= C (M_mu e^(-mu m))^k`, an exponential growth bound. That is not a
  closing.

The dying step is therefore the same for every member: `k` first-entry steps
cover the level-reach event, whose probability stays at least `theta`.

## Item 5: Hölder closings

**The bound.** Let `Q_J` act on row vectors, `(nu Q_J)(y) = sum_x nu(x) Q_J(x,y)`.
Write `f_z = T^J delta_z`, so `f_z(y) = T^J(y,z)`. By item 1, with `x = o`,

```text
tau_p(o,z) <= sum_(k >= k_0) <delta_o Q_J^k, f_z> <= sum_(k >= k_0) ||Q_J||_(q'->q')^k ||f_z||_q,
```

where `k_0 = (h(z)-J)/(J+K)`. The second step is Hölder,
`||delta_o||_(q') = 1`, and submultiplicativity of the operator norm.

For `q = infinity`, `q' = 1`, and `||Q_J||_(1->1) = sup_x sum_y Q_J(x,y) = G(J)`.
By item 4 this is `>= 1`. So the `q = infinity` closing is the scalar one,
and it is dead.

**The slab factor.** By translation invariance,

```text
||f_z||_q^q = sum_(y : -K < h(z)-h(y) < J) tau_p(y,z)^q = sum_(w : -J < h(w) < K) tau_p(o,w)^q.
```

Here `w = z^(-1) y`, and we used `tau_p(y,z) = tau_p(z,y) = tau_p(o, z^(-1) y)`.
This is a sum over finitely many levels `{h = j}`, and it does not depend on
`z`.

**Level independence.** Let `g` have `h(g) = j`. By Harris–FKG,

```text
tau_p(o, yg) >= tau_p(o,y) tau_p(y,yg) = tau_p(o,y) tau_p(o,g),
```

and `tau_p(o,g) >= p^(|g|) > 0`. Summing over `h(y) = 0` gives

```text
kappa_q(p) <= tau_p(o,g)^(-q) sum_(h(y') = j) tau_p(o,y')^q.
```

The same argument with `g^(-1)` gives the reverse bound. So each level sum is
finite iff `kappa_q(p)` is finite. Levels outside `h(Gamma)` are empty. Hence
the slab factor is finite iff `kappa_q(p) < infinity`.

**The route therefore needs both of these:**
- `||Q_J||_(q'->q') < 1` for some `J`;
- `kappa_q(p) < infinity`, since otherwise `||f_z||_q = infinity` and the
  bound is void.

**The slab input alone gives `p <= p_u`.** Let `p > p_u`. By uniqueness and
Harris–FKG,

```text
tau_p(o,y) >= P(o <-> infinity, y <-> infinity) >= theta^2
```

for every `y`. The level `{h = 0} = ker h` is infinite, since `Gamma` is
nonamenable and `Z` is amenable, so `ker h` is nonamenable. Hence
`kappa_q(p) >= |ker h| theta^(2q) = infinity`.

So `kappa_q(p) < infinity` at one `p > p_c` gives `p_c < p <= p_u`, with no
use of `Q_J`. The operator half-space route reduces the flagship only to an
input that proves it outright. This proves item 5.

**What the route does give.** When both inputs hold, it gives
`tau_p(o,z) <= C r^(h(z)/(J+K))` with `r = ||Q_J||_(q'->q') < 1`. For
`h(z) != 0`, this means `sum_n tau_p(o,z^n) < infinity`, which is the
relative gap along `<z>`. That is recorded as not claimed in the target.

## Calibration on `T_4`

Take `G = Cay(F_2, {a^(±1), b^(±1)})`, the `4`-regular tree, with `h(a) = 1`
and `h(b) = 0`. So `K = 1`. Then `tau_p(o,y) = p^(|y|)`, `p_c = 1/3` and
`p_u = 1`.

**`G(n) = infinity` for `p > 1/3`.** For `L >= 2`, let `W_L` be the set of
reduced words of length `L` that satisfy all of the following:
- they start and end with `a^(-1)`;
- every prefix has height `<= 0`;
- the whole word has height `<= 0`.

Concatenating words of `W_L` gives reduced words, since `a^(-1) a^(-1)` does
not cancel, and the height stays `<= 0`. So from `o`, the words of `W_L`
concatenated span a subdivided `|W_L|`-ary tree inside `{h <= 0} ⊂ L_n`.

Along a uniform reduced word, the height increments form a mean-zero
Markov-additive walk on the finite state space of last letters. The
probability of staying `<= 0` for `L` steps, with the endpoint constraints,
decays only polynomially. This is the standard ballot estimate for such
walks. So `|W_L|^(1/L) -> 3`.

The subdivided tree percolates when `p^L |W_L| > 1`, and this holds for large
`L` when `p > 1/3`. So the lower half-space percolates from `o`, and item 3
gives `G(n) = infinity`. This is consistent with item 4.

This is a calibration, not a load-bearing step. The kill uses only items 1,
2 and 4.

**The `q = 2` route runs exactly on `(1/3, 1/sqrt 3)`.**
- **The slab factor.** The number of reduced words of length `n` and height
  `0` is `3^n n^(-1/2)` up to constants, by the local limit theorem for the
  same Markov-additive walk. So `kappa_2(p) = sum_(h(y)=0) p^(2|y|)` is finite
  iff `3p^2 < 1`, and it diverges at `p = 1/sqrt 3`.
- **The operator.** `FE_J(o) ⊂ {|y| >= J}`, and
  `Q_J(x,y) <= tau_p(x,y) = p^(|x^(-1)y|)`. So, entrywise,
  `Q_J <= sum_(n >= J) p^n A_n`, where `A_n` is convolution by the indicator
  of the sphere `S_n`. For nonnegative kernels, entrywise domination gives
  norm domination. Haagerup's inequality gives
  `||A_n||_(2->2) <= (n+1) |S_n|^(1/2) = (n+1) (4 3^(n-1))^(1/2)`. Hence
  ```text
  ||Q_J||_(2->2) <= sum_(n >= J) (n+1) p^n (4 3^(n-1))^(1/2),
  ```
  which tends to `0` as `J -> infinity` when `p sqrt 3 < 1`.

So both inputs hold exactly on `(1/3, 1/sqrt 3)`, and `1/sqrt 3 = p_(2->2)(T_4)`.
On that interval, `kappa_2 < infinity` already certifies `p < p_u`, as item 5
says. Nothing on `T_4` contradicts items 1–5.

**Where the calibration of the lemma enters.** On the `3`-regular tree with a
Busemann height, clusters above `p_c` are bounded above. So item 2 fails
there, and a half-space renewal in a Busemann height is not killed by this
argument. Such heights are not homomorphisms of a unimodular group, and they
are outside the target. See `fpbs-boundary-tilted-susceptibility-kernel`.
