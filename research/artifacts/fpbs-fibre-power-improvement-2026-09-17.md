# Fibre-mass power improvement below the relative threshold, and p_{2->2} = p_u as a square-root law

Worker swarm-0917-w5-bs-wq-normal, 2026-09-17.

## 0. Setting and notation

* `Gamma` is finitely generated, `S` is a finite symmetric generating set, and
  `G = Cay(Gamma,S)`.
* `N` is a normal subgroup, `Q = Gamma/N` and `pi : Gamma -> Q`. `Gamma_q` is the
  coset over `q`.
* `P_p` is Bernoulli(`p`) bond percolation, `K_o` is the cluster of `o`, and
  `tau_p(x,y) = P_p(x <-> y)`.
* `sigma_p(q) = E_p|K_o ∩ Gamma_q|` and `A_q = {o <-> Gamma_q}`.
* `X = |K_o ∩ N|` and `Y_q = |K_o ∩ Gamma_q|`.
* `p_c(N;G)` is the relative critical threshold of `fpbs-amenable-wq-normal-pu-is-relative-pc`.
  By `fpbs-hp-relative-sharpness`, for
  `p < p_c(N;G)`, `X` has an exponential tail, so `E_p X^r < infinity` for every
  `r >= 1`.
* For a nonnegative function `f` on `Q`, `r*(f) = inf{r >= 1 : sum_q f(q)^r < infinity}`
  (`infinity` if there is none), and `r*(p) = r*(sigma_p)`.

Two imported inputs:

* **(G) Thinning inequality.** Grimmett, *Percolation*, 2nd ed., Theorem 2.38,
  used in this form by Hutchcroft--Pan arXiv:2412.15895, Section 3. If `A` is
  increasing, then `P_{p^theta}(A) >= P_p(A)^theta` for all `p, theta in [0,1]`.
  The theorem is stated for events depending on finitely many edges.
  `A_q = {o <-> Gamma_q}` is the increasing union of the events
  `{o <-> Gamma_q inside the ball B(o,m)}`, and the inequality passes to the limit.
* **(H) Haagerup's inequality on `F_n`.** If `f` is supported on the sphere
  `S_Q(R)`, then `||lambda(f)||_{2->2} <= (R+1) ||f||_2`.

## 1. Theorem 1: every coset moment is largest on the subgroup

**Theorem 1.** Let `N` be normal, `0 < p <= 1` and `r >= 1`. Then
`E_p[Y_q^r] <= E_p[X^r]` for every `q in Q`. Hence, for every `lambda >= 0`,
`E_p e^(lambda Y_q) <= E_p e^(lambda X)`. In particular, for `p < p_c(N;G)` there
are `C, c > 0` with `sup_q P_p(|K_o ∩ Gamma_q| >= n) <= C e^(-cn)`.

*Proof.* This is the proof of `fpbs-normal-fibre-second-moment-maximal-proof`,
with Hölder's inequality in place of Cauchy--Schwarz.

1. Assume `M := E X^r < infinity`. Step 1 of that proof uses only
   `E X <= M^(1/r) < infinity`, and gives `Y_q < infinity` and `Z := Y_(q^-1) < infinity`
   almost surely.
2. Fix `q` and put `A_x = |K_x ∩ xN|` and `B_x = |K_x ∩ xqN|`. Define
   `m(x,y) = 1{x <-> y} 1{y in xqN} A_x^(r-1) 1{A_x <= n, B_x <= n}`.
   This is bounded and diagonally invariant.
   * The outgoing mass at `o` is `Y X^(r-1) 1{X <= n, Y <= n}`.
   * The incoming mass at `o` sums over `x in K_o ∩ q^(-1)N`. By normality each
     such `x` has `A_x = Z` and `B_x = X`, so the incoming mass is `Z^r 1{X <= n, Z <= n}`.

   Write `A_n = {X <= n, Y <= n}` and `B_n = {X <= n, Z <= n}`. The mass-transport
   principle gives `E[X^(r-1) Y; A_n] = E[Z^r; B_n]`. Swapping `q` and `q^(-1)`
   gives `E[X^(r-1) Z; B_n] = E[Y^r; A_n]`.
3. Put `a = E[Z^r; B_n]` and `b = E[Y^r; A_n]`, both finite. Hölder with exponents
   `r/(r-1)` and `r` gives `a <= M^(1-1/r) b^(1/r)` and `b <= M^(1-1/r) a^(1/r)`.
   So `a <= M^(1-1/r^2) a^(1/r^2)`, and therefore `a <= M`. Likewise `b <= M`.
4. Monotone convergence as `n -> infinity` gives `E Y_q^r <= M`.

The exponential-moment bound follows by expanding over integer `r`. The tail
bound follows from Markov's inequality, using `E e^(lambda X) < infinity` for
small `lambda > 0` (`fpbs-hp-relative-sharpness`). ∎

**Corollary 1.1.** For `p < p_c(N;G)`, every `r > 1` and every `q`,

```text
P_p(A_q) <= sigma_p(q) <= (E_p X^r)^(1/r) P_p(A_q)^(1 - 1/r).
```

*Proof.* `E Y = E[Y 1{Y>0}] <= (E Y^r)^(1/r) P(Y>0)^(1-1/r)`, then Theorem 1. ∎

So the fibre-mass profile `sigma_p` and the fibre-hitting profile `P_p(A_.)` have
the same exponent: `r*(sigma_p) = r*(P_p(A_.))`.

## 2. Theorem 2: power improvement in p

**Theorem 2.** Let `N` be normal and `p < p_c(N;G)`, `p < p' < 1`, and put
`s_0 = log p / log p' > 1`. For every `1 <= s < s_0` there is `C = C(p,p',s)` with

```text
sigma_p(q) <= C sigma_(p')(q)^s        for all q in Q.
```

*Proof.* Put `theta = log p' / log p in (0,1)`, so `p^theta = p'`. By (G),
`P_(p')(A_q) >= P_p(A_q)^theta`, that is, `P_p(A_q) <= P_(p')(A_q)^(s_0)`.
Choose `r` with `(1-1/r) s_0 = s`. Corollary 1.1 at `p` gives

```text
sigma_p(q) <= (E_p X^r)^(1/r) P_(p')(A_q)^s <= (E_p X^r)^(1/r) sigma_(p')(q)^s,
```

using `P_(p')(A_q) <= sigma_(p')(q)`. ∎

Only `p` has to lie below the relative threshold; `p'` is arbitrary.

**Corollary 2.1 (exponent monotonicity).** For `p < p' < p_c(N;G)`,

```text
r*(p) <= r*(p') · log p' / log p.
```

Equivalently, `p -> r*(p) log(1/p)` is nondecreasing on `(0, p_c(N;G))`.

*Proof.* Take `r > r*(p')` and `s < s_0`. Then
`sum_q sigma_p(q)^(r/s) <= C^(r/s) sum_q sigma_(p')(q)^r < infinity`, so
`r*(p) <= r/s`. Now let `r` decrease to `r*(p')` and `s` increase to `s_0`. ∎

This is the fibre-summed form of Hutchcroft--Pan's step
`beta*_{p^theta} <= theta beta*_p` (arXiv:2412.15895, Section 3). It holds over every
normal subgroup, with no tree structure and no nonunimodularity. The only extra
input is Theorem 1, which replaces their slab bound `E_p(n) <= C P_p(n) log(e/P_p(n))`.

## 3. Two operator comparisons over an amenable normal kernel

Let `T_p` be the connectivity operator on `l2(Gamma)`, with kernel `tau_p`, and let
`p_{2->2} = sup{p : ||T_p||_{2->2} < infinity}`.

**Lemma 3.1 (block domination, any normal `N`).**
`||T_p|| <= ||lambda_Q(sigma_p)||_{2->2}`.

*Proof.*
* Split `f in l2(Gamma)` over cosets and put `F(q) = ||f|_{Gamma_q}||_2`. The
  block of `T_p` from `Gamma_(q')` to `Gamma_q` has row sums and column sums
  `sum_(y in Gamma_(q')) tau(x,y) = sigma_p(q^(-1) q')`, by translation invariance
  and normality.
* By Schur's test that block has norm at most `sigma_p(q^(-1)q')`.
* Hence `||(T_p f)|_{Gamma_q}|| <= sum_(q') sigma_p(q^(-1)q') F(q')`.
* The right side is a convolution of `F` by `sigma_p` on `Q`. Its operator norm on
  `l2(Q)` equals `||lambda_Q(sigma_p)||`: right and left convolution are conjugate
  under the inversion `q -> q^(-1)`, and `sigma_p(q) = sigma_p(q^(-1))`. ∎

**Lemma 3.2 (Følner lower bound, amenable normal `N`).**
`||T_p||^2 >= sum_q sigma_p(q)^2`.

*Proof.* Assume `||T_p|| < infinity`.
1. Let `F ⊂ N` be finite and put `f = |F|^(-1/2) 1_F`. Fix a finite set `J ⊂ Q`
   and representatives `g_q` of the cosets.
2. Since `||f|| = 1`, restrict `||T_p f||^2` to the sets `F g_q`, which lie in
   the coset over `q` and have size `|F|`. Cauchy--Schwarz over each set gives

   ```text
   ||T_p||^2 >= ||T_p f||^2 >= sum_(q in J) |F|^(-2) ( sum_(k,h in F) tau(k g_q, h) )^2 .
   ```
3. By invariance, `tau(k g_q, h) = tau(o, g_q^(-1) k^(-1) h)`.
4. Fix a finite `B ⊂ N`. Keeping only the terms `h = kb` with `b in B` and
   `kb in F`,

   ```text
   |F|^(-1) sum_(k,h in F) tau(o, g_q^(-1) k^(-1) h) >= sum_(b in B) tau(o, g_q^(-1) b) |F ∩ F b^(-1)| / |F|.
   ```

   Along a right Følner sequence for `N` the ratios tend to `1`.
5. Let `B` increase to `N` and `J` increase to `Q`. Then
   `||T_p||^2 >= sum_q sigma_p(q^(-1))^2 = sum_q sigma_p(q)^2`. ∎

## 4. Theorem 3: over a free quotient with tree-projected generators, p_{2->2} = p_u is a square-root law

**Setting (TP).**
* `N` is an infinite amenable normal subgroup of `Gamma`.
* `Q = Gamma/N` is free of rank `n >= 2`, with basis `B`.
* `pi(S) ⊆ {1} ∪ B ∪ B^(-1)`.

This covers every Cayley graph of `fpbs-tree-projected-cayley-graphs-strict-thresholds`,
including the rigid decorations of `fpbs-tree-projected-rigid-decorations-strict-thresholds`
such as `S_rig`. Normal subgroups are wq-normal, so
`fpbs-amenable-wq-normal-pu-is-relative-pc` gives `p_u = p_c(N;G)`.

**Lemma 4.1 (cut submultiplicativity).** In (TP), let `p < p_u` and let `w`, `u`
be reduced words in `Q` with `|wu| = |w| + |u|`. Then
`sigma_p(wu) <= sigma_p(w) sigma_p(u)`. So `b_R(p) = sum_(|q|=R) sigma_p(q)^2`
satisfies `b_(R+R') <= b_R b_(R')`.

*Proof.*
* Every edge of `G` projects to an edge or a loop of the Cayley tree of `Q`.
  So every open simple path from `o` to `Gamma_(wu)` visits `Gamma_w`.
* Let `x` be the first such visit. The path splits into edge-disjoint pieces
  from `o` to `x` and from `x` to the endpoint. By BK,
  `tau(o,y) <= sum_(x in Gamma_w) tau(o,x) tau(x,y)`.
* Sum over `y in Gamma_(wu)`. Since `x^(-1) Gamma_(wu) = Gamma_u` for
  `x in Gamma_w`, the inner sum is `sigma_p(u)`, and the outer sum is `sigma_p(w)`.
* Each reduced word of length `R+R'` splits uniquely as `wu` with `|w| = R` and
  `|u| = R'`, which gives the second statement. ∎

**Lemma 4.2.** In (TP), for `p < p_u`:
`||T_p|| < infinity` if and only if `sigma_p ∈ l2(Q)`.

*Proof.*
* **Only if.** Lemma 3.2.
* **If.** Suppose `sum_R b_R < infinity`.
  1. Then `b_(R_0) < 1` for some `R_0`. By Lemma 4.1, `b_R <= C beta^R` with
     `beta = b_(R_0)^(1/R_0) < 1` and `C = max_(j < R_0) b_j / beta^j`.
  2. (H) gives `||lambda_Q(sigma_p)|| <= sum_R (R+1) (C beta^R)^(1/2) < infinity`.
  3. Lemma 3.1 then gives `||T_p|| < infinity`. ∎

**Theorem 3.** In (TP), the following are equivalent:

* **(a)** `p_{2->2}(G) = p_u(G)`;
* **(b)** (square-root law) for every `p < p_u` and every `r > 2`,
  `sum_(q in Q) P_p(o <-> Gamma_q)^r < infinity`;
* **(b')** the same statement with `sigma_p(q)` in place of `P_p(o <-> Gamma_q)`;
* **(c)** `liminf_(p -> p_u^-) r*(p) <= 2`.

Moreover, unconditionally,

```text
p_{2->2}(G) >= sup_(p' < p_u) (p')^(max(r*(p'), 2)/2).
```

*Proof.*
* **(b) ⇔ (b').** Corollary 1.1 gives `r*(sigma_p) = r*(P_p(A_.))`.
* **(b') ⇒ (c).** Immediate.
* **(a) ⇒ (b').** For `p < p_u = p_{2->2}` we have `||T_p|| < infinity`. Lemma 4.2
  gives `sigma_p ∈ l2 ⊂ l^r`.
* **Quantitative bound.** Let `p' < p_u`.
  * If `r*(p') < 2`, then `sigma_(p') ∈ l2`, so `p' <= p_{2->2}` by Lemma 4.2.
  * If `2 <= r*(p') < infinity`, take `p < (p')^(r*(p')/2) <= p'`.
    1. Then `log p' / log p < 2 / r*(p')`, so Corollary 2.1 gives `r*(p) < 2`.
    2. Hence `sigma_p ∈ l2(Q)`, and Lemma 4.2 gives `||T_p|| < infinity`.
    3. So `p <= p_{2->2}`.
  * If `r*(p') = 2`, then `sigma_p ∈ l2` for every `p < p'` by the same step, so
    `p_{2->2} >= p'`.
* **(c) ⇒ (a).** We already know `p_{2->2} <= p_u`, so fix `p < p_u`.
  1. The ratio `log p_u / log p` is below 1. Choose `delta > 0` with
     `2/(2+delta) > log p_u / log p`.
  2. By (c) there is `p' in (p, p_u)` with `r*(p') < 2 + delta` and
     `log p' / log p < 2/(2+delta)`.
  3. Corollary 2.1 gives `r*(p) < 2`, so `sigma_p ∈ l2(Q)` and
     `||T_p|| < infinity` by Lemma 4.2.
  4. Since `p < p_u` was arbitrary, `p_{2->2} >= p_u`. ∎

**Remarks.**
1. **What Theorem 3 upgrades.** It turns a non-strict square-root law into a
   strict one: `r* <= 2` below `p_u` gives `r* < 2`, hence `l2`. This is the
   strictness step of Hutchcroft--Pan (their monotonicity of `beta*` together with
   `beta* >= 1/2` below `p_u`). Here it is proved on *unimodular* graphs with
   discrete automorphism group, such as `S_rig`. There the end-fixing symmetry
   they use is absent (`fpbs-tree-projected-rigid-decorations-discrete-automorphisms`).
2. **What is left.** Question Q of
   `research/artifacts/fpbs-amenable-normal-fibre-mass-bound-2026-09-16.md` §5.2 is
   `p_{2->2} = p_u`. On (TP) graphs it is exactly the non-strict square-root law
   (b). That law is Hutchcroft--Pan's backscattering statement
   `beta* >= 1/2 below p_u`, fibre-summed. It remains open on (TP) graphs that
   Hutchcroft--Pan do not cover.
3. **Consequence for the hole.** On (TP) graphs, `fpbs-amenable-wq-normal-relative-subcriticality`
   is `p_c < p_u`. Assume (b). Then the hole is equivalent to `p_c < p_{2->2}`, and
   by `fpbs-tree-projected-sphere-bubble-l2-equivalence` to the critical sphere
   bubble `b_R(p_c) < 1` for some `R`. So on these graphs no target strictly
   between the hole and critical L2 exists, unless the square-root law fails.

## 5. Where backscattering stops on (TP) graphs

The natural proof of (b) follows Hutchcroft--Pan Section 4. Suppose (b) fails at
some `p < p_u`, so `r*(p) > 2`. By Corollary 2.1, `r*(p'') >= r*(p) log p / log p'' > r*(p)` for every
`p'' in (p, p_u)`, so the failure persists at larger parameters with a margin. Lemma 4.1, with exponent `r` in place of 2,
makes `sum_(|q|=R) sigma_p(q)^r` submultiplicative, and for some `r > 2` its
exponential rate is at least 1. By Corollary 1.1 the same holds for the hitting
probabilities. For `g ∈ N` central, Harris--FKG gives
`P(o <-> Gamma_q, g <-> Gamma_q) >= P(A_q)^2`. So `K_o` and `K_g` hit
exponentially many common fibres on the sphere.

**What transfers.**
* When `N` is central, the translate by `g` of the event `{o -> y}` is
  `{g -> yg}`. So the pair `(y, yg)` keeps the separation `g` exactly, and no flat
  lemma is needed to hold the pair together.
* Sprinkling along infinitely many independent common fibres merges the two
  clusters almost surely. That gives `inf_g tau_(p'')(o,g) > 0` at `p'' > p`, so
  `E_(p'') X = infinity` and `p'' >= p_u`, a contradiction.

**Where it stops.** A branching process needs children in disjoint slabs, hence
at most one child per fibre.
* Exact-translate children give mean offspring
  `sum_q P(exists h: o -> g_q h and g -> g_q h g)`. FKG bounds this below only by
  `sum_q max_h a(g_q h)^2`, not by `sum_q P(A_q)^2`. The loss is the height spread
  of `K_o ∩ Gamma_q`.
* Rigid decorations have height drift. The drift cancels in the separation
  `h_g - h_o`, but that separation is a correlated difference, not a symmetric
  random walk, so the Kesten return step of Hutchcroft--Pan has no input.
* A second-moment count of coincident fibres instead involves same-fibre sibling
  lineages. Their contribution grows at the rate of `b_R` itself, so the second
  moment is not dominated by the square of the first.

The precise missing input is a **flat pair lemma**. Below `p_u`, if
`sum_(|q|=R) P_p(A_q)^2` grows exponentially, then so does
`sum_(|q|=R) P_p(o -> g_q h and g -> g_q h g for some h)`, uniformly in `g ∈ N`.
