# Sphere cuts and exponential decay of critical fibre tails

Lane `bs-rd-weighted-bubble`, 2026-09-12. The setting and notation are those of
`research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md` and
`research/artifacts/fpbs/docs/rd-weighted-fibre-bubble-criterion.md`: `Gamma`
finitely generated, `S` a finite symmetric generating set, `X = Cay(Gamma,S)`,
`H` normal in `Gamma`, `Q = Gamma/H` with word length `|.|` from `pi(S)`,
`Gamma_q = pi^(-1)(q)`, and

    sigma_p(q)   = sum_{x in Gamma_q} tau_p(o,x),
    sigma_{p,R}  = sigma_p 1_{S_Q(R)},          b_R(p) = ||sigma_{p,R}||_2^2,
    T_m(p)       = sum_{|q| >= m} sigma_p(q)^2,  B_p = T_0(p),
    (lambda(f) g)(q) = sum_{q'} f(q') g(q'^(-1) q)   on l2(Q).

The RD criterion artifact recorded, for one-ended quotients: "no fibre separates
X ... no replacement for the cut structure". A single fibre does not separate
`X`, but the fibre saturation `pi^(-1)(S_Q(R))` of a sphere always does. That
gives a tail inequality with one operator-norm factor, and the inequality
bootstraps one finite-radius estimate into exponential decay of every critical
fibre tail. Over a quotient with rapid decay, the open weighted premise becomes
equivalent to a statement at a single radius. Nothing here is refereed or
formalized.

## 1. The sphere cut inequality

**Lemma 1.1.** For every `p`, every `R >= 0` and every `q` with `|q| >= R`,

    sigma_p(q)  <=  sum_{q' in S_Q(R)} sigma_p(q') sigma_p(q'^(-1) q),

and every `q'` in the sum has `|q'^(-1) q| >= |q| - R`.

*Proof.*
1. **Cut.** Along an edge `g ~ gs` of `X`, `pi(gs) = pi(g) pi(s)`, and `pi(s)` is
   a generator of `Q` or trivial, so `|pi(.)|` changes by at most one. A path from
   `o` (level 0) to `x in Gamma_q` (level `|q| >= R`) therefore visits the level
   `pi^(-1)(S_Q(R))`.
2. **BK.** If `o <-> x`, choose a simple open path and let `y` be its first vertex
   at level `R`. The segments `o -> y` and `y -> x` are open and edge-disjoint, so
   `{o <-> y} o {y <-> x}` occurs. Countable subadditivity and the van den
   Berg–Kesten inequality give
   `tau_p(o,x) <= sum_{y in pi^(-1)(S_Q(R))} tau_p(o,y) tau_p(y,x)`.
3. **Transitivity.** Left multiplication by `y^(-1)` is an automorphism of `X`
   and, `H` being normal, maps `Gamma_q` onto `Gamma_{pi(y)^(-1) q}`. So
   `sum_{x in Gamma_q} tau_p(y,x) = sigma_p(pi(y)^(-1) q)`. Sum over
   `x in Gamma_q` and group the `y` by their fibre `q' = pi(y)`.
4. **Length.** `|q| <= |q'| + |q'^(-1) q| = R + |q'^(-1) q|`. QED.

**Lemma 1.2 (tail inequality).** For `p < p_c` and all `R, m >= 0`,

    T_{R+m}(p)  <=  ||lambda(sigma_{p,R})||_{2->2}^2  T_m(p).

*Proof.* For `p < p_c`, `sum_q sigma_p(q) = chi_p < infinity` (sharpness of the
phase transition on transitive graphs), so `sigma_p` lies in `l1(Q)`, hence in
`l2(Q)`, and every quantity is finite. For `|q| >= R + m`, Lemma 1.1 and its
length bound give

    sigma_p(q)  <=  ( lambda(sigma_{p,R}) (sigma_p 1_{|.| >= m}) )(q),

because every `q'^(-1) q` that occurs has length at least `m`. Both sides are
nonnegative. Squaring and summing over `|q| >= R + m`,
`T_{R+m} <= ||lambda(sigma_{p,R}) (sigma_p 1_{|.|>=m})||_2^2`
`<= ||lambda(sigma_{p,R})||^2 T_m`. QED.

**Remarks.**
* On tree-projected generating sets single fibres are cuts, and
  `b_{R+R'} <= b_R b_{R'}`. Lemma 1.2 holds for every quotient. What it costs is
  the operator norm `||lambda(sigma_R)||` in place of `b_R^(1/2)`.
* **Monotonicity.** If `0 <= f <= g` entrywise, then `||lambda(f)|| <= ||lambda(g)||`,
  since `|<u, lambda(f) v>| <= <|u|, lambda(g) |v|>`. In particular
  `p -> ||lambda(sigma_{p,R})||` is nondecreasing.

## 2. Bootstrap to exponential decay

**Theorem 2.1.** Let `Gamma`, `S`, `H` be arbitrary; no hypothesis on `Q` is
used. Suppose that for some `R_0 >= 1`

    theta  :=  ||lambda(sigma_{p_c,R_0})||_{2->2}^2  <  1.

Then there is `M < infinity` with

    T_m(p_c)  <=  M theta^(floor(m/R_0))      for all m >= 0,

and hence `sum_q (1+|q|)^s sigma_{p_c}(q)^2 < infinity` for every `s >= 0`.

*Proof.*
1. **Uniformity below `p_c`.** `sigma_p <= sigma_{p_c}` entrywise, so by
   monotonicity `||lambda(sigma_{p,R_0})||^2 <= theta` for every `p < p_c`.
2. **Iteration.** Lemma 1.2 with `R = R_0` gives
   `T_{m+R_0}(p) <= theta T_m(p)`, hence `T_m(p) <= theta^(floor(m/R_0)) B_p`.
3. **Uniform bound on `B_p`.**
   `B_p = sum_{|q| < R_0} sigma_p(q)^2 + T_{R_0}(p) <= sum_{|q|<R_0} sigma_p(q)^2 + theta B_p`,
   so `B_p <= (1-theta)^(-1) sum_{|q|<R_0} sigma_p(q)^2`.
   * Fix `q_0 in S_Q(R_0)`. For `|q| < R_0` fix `g_q in Gamma` with
     `pi(g_q) = q^(-1) q_0`, and let `L = max_q |g_q|_S`.
   * `x -> x g_q` maps `Gamma_q` bijectively onto `Gamma_{q_0}`.
   * By Harris–FKG applied to `{o <-> x}` and a fixed open path from `x` to `x g_q`,
     `tau_p(o, x g_q) >= p^L tau_p(o,x)`. Summing, `sigma_p(q) <= p^(-L) sigma_p(q_0)`.
   * Also `b_{R_0}(p) = ||lambda(sigma_{p,R_0}) delta_1||^2 <= theta`.
   * So for `p in [p_c/2, p_c)`,
     `B_p <= M := (1-theta)^(-1) |B_Q(R_0)| (p_c/2)^(-2L)`.
4. **Limit.** `T_m(p) <= M theta^(floor(m/R_0))` uniformly on `[p_c/2, p_c)`. Each
   `sigma_p(q)` is nondecreasing and left-continuous in `p`. By monotone
   convergence `T_m(p_c) = lim_{p -> p_c-} T_m(p)`, and the bound passes to `p_c`.
   Finally `sum_q (1+|q|)^s sigma_{p_c}(q)^2 <= sum_m (1+m)^s T_m(p_c)
   <= M sum_m (1+m)^s theta^(floor(m/R_0)) < infinity`. QED.

**Corollary 2.2 (necessary rate; subexponential quotients excluded).** Put
`h(Q) = lim_R (1/R) log |S_Q(R)|`. Under the hypothesis of Theorem 2.1,
`theta^(1/R_0) >= e^(-h(Q))`. In particular, if `Q` has subexponential growth,
`||lambda(sigma_{p_c,R})|| >= 1` for every `R >= 1`.

*Proof.* By Cauchy–Schwarz on spheres,
`sum_{|q|=m} sigma_{p_c}(q) <= |S_Q(m)|^(1/2) T_m(p_c)^(1/2)`. If
`theta^(1/R_0) < e^(-h(Q))`, the right side is summable in `m`. Then
`chi_{p_c} = sum_q sigma_{p_c}(q)` is finite. But `chi_p >= c/(p_c - p)` on every
transitive graph (Aizenman–Newman), so `chi_{p_c} = infinity`. QED.

## 3. Equivalence over rapid-decay quotients

**Theorem 3.1.** Let `Q` have rapid decay with constants `C, D`: every `f`
supported in `B_Q(R)` has `||lambda(f)|| <= C (1+R)^D ||f||_2`. The following are
equivalent on `Cay(Gamma,S)`:

* **(a)** `W_D(p_c) = sum_q (1+|q|)^(2D+2) sigma_{p_c}(q)^2 < infinity`, the open
  premise `fpbs-rd-quotient-weighted-critical-fibre-bubble`;
* **(b)** `C^2 (1+R_0)^(2D) b_{R_0}(p_c) < 1` for some `R_0 >= 1`;
* **(c)** `||lambda(sigma_{p_c,R_0})|| < 1` for some `R_0 >= 1`;
* **(d)** `T_m(p_c)` decays exponentially in `m`;
* **(e)** `sum_q (1+|q|)^s sigma_{p_c}(q)^2 < infinity` for every `s >= 0`.

*Proof.*
* (b) ⟹ (c): rapid decay for the sphere-supported `sigma_{p_c,R_0}` gives
  `||lambda(sigma_{p_c,R_0})||^2 <= C^2 (1+R_0)^(2D) b_{R_0}(p_c)`.
* (c) ⟹ (d) and (e): Theorem 2.1.
* (d) ⟹ (e) ⟹ (a): summation by parts, as in step 4.
* (a) ⟹ (b): `(1+R)^(2D+2) b_R(p_c) <= W_D(p_c)`, so
  `C^2 (1+R)^(2D) b_R(p_c) -> 0` and (b) holds for all large `R_0`. QED.

**Consequences.**
* **No cut structure is needed.** The obstruction recorded for one-ended
  quotients disappears. Fibre-saturated spheres are cuts in every Cayley graph
  over every quotient.
* **One scale.** Over the hyperbolic-quotient class (`F_2 x Z`, Seifert-fibred
  groups, `hyperbolic x K`, central extensions) the premise is equivalent to a
  single finite-radius quantity: some `R_0` with
  `||lambda_Q(sigma_{p_c} 1_{S_Q(R_0)})|| < 1`, for instance through
  `b_{R_0}(p_c) < C^(-2) (1+R_0)^(-2D)`. This is a reformulation of the premise at
  one radius, not a weaker premise.
* **Dichotomy.** Over a rapid-decay quotient, exactly one of these holds:
  * critical fibre tails decay exponentially;
  * `C^2 (1+R)^(2D) b_R(p_c) >= 1` for every `R >= 1`, i.e. critical sphere
    bubbles are at least `C^(-2) (1+R)^(-2D)` at every radius.
* **Tree-projected class.** There the finite-radius criterion is
  `b_{R_0}(p_c) < 1` with no polynomial factor, because fibres themselves are cuts.
  For free quotients, Haagerup's inequality (`||lambda(f)|| <= (R+1) ||f||_2` for
  `f` supported on the sphere of radius `R`) gives the explicit form
  `(1+R_0)^2 b_{R_0}(p_c) < 1` of (b), valid on every generating set.

## 4. What remains

The open claim `fpbs-critical-sphere-fibre-operator-below-one`: for every `Gamma`
with an infinite normal subgroup and non-elementary hyperbolic quotient, and every
`S`, some `R_0 >= 1` has `||lambda_Q(sigma_{p_c} 1_{S_Q(R_0)})||_{2->2} < 1`.

**Explicit sufficient forms**, by rapid decay and `b_R <= T_R`:
* `b_{R_0}(p_c) < C^(-2) (1+R_0)^(-2D)`;
* `T_{R_0}(p_c) < C^(-2) (1+R_0)^(-2D)`.

**Necessary:** the decay exponent is at most `h(Q)` (Corollary 2.2).

**Attempts.**
* **Mean-field profile.** For critical branching random walk the fibre occupation
  is the projected Green function. Its sphere bubbles decay exponentially, so the
  condition holds for large `R_0`. **Where it stops:** the comparison is a
  triangle-type input.
* **From the unweighted bubble.** `B_{p_c} < infinity` is necessary for the L2 gap
  when `H` is amenable. It gives `T_R(p_c) -> 0` with no rate. Theorem 3.1 needs
  the rate `(1+R)^(-2D)` at a single radius. **Where it stops:** no rate.
* **Differential inequality.** Russo plus BK bound the growth of
  `||lambda(sigma_{p,R})||` through `||S_p||`, the same L2 barrier as before.
* **Geodesic prefixes (heuristic, not proved).** In a `delta`-hyperbolic `Q` the
  terms of Lemma 1.1 with `q'` far from a geodesic prefix of `q` have excess length
  `|q'^(-1) q| - (|q| - R) > 0`. Charging them against pointwise decay of
  `sigma_{p_c}` would replace the operator norm by a constant times `b_R`. **Where it
  stops:** that pointwise decay is exactly what is missing.

## 5. Trust surfaces

* BK on infinite graphs, sharpness (`chi_p < infinity` for `p < p_c`), and
  Aizenman–Newman's lower bound on `chi_p`, which is used only in Corollary 2.2:
  all standard.
* Rapid decay for hyperbolic groups is the imported
  `hyperbolic-groups-have-property-rd`.
* Novelty is not checked. The sphere-cut BK step is standard, and the rapid-decay
  bootstrap may already exist in the literature.
