---
rg: 2
id: fpbs-percolation-kesten-normal-gap
kind: claim
title: Percolation Kesten criterion, a normal subgroup with nonamenable quotient has a strictly larger relative threshold
distinct_from:
  fpbs-tree-normal-relative-threshold-is-inverse-cogrowth: that proves the statement on the free-group tree, where the relative threshold is the inverse cogrowth; this asserts the strict gap on every Cayley graph of every group.
  fpbs-hyperbolic-quotient-every-generating-set: that is the gap for groups with a non-elementary hyperbolic quotient; this is one percolation statement for every nonamenable quotient, and it implies that claim through the separation criterion.
  fpbs-amenable-wq-normal-relative-subcriticality: that asks for finite relative susceptibility along an amenable wq-normal subgroup; this asks for the threshold gap along any infinite normal subgroup, amenable or not, provided the quotient is nonamenable.
  fpbs-relative-gap-along-any-subgroup-separates: that turns a relative gap into p_c < p_u; this is the proposed universal source of such gaps.
---

**OPEN.** Let `Gamma` be finitely generated, and let `N` be an infinite normal
subgroup such that `Gamma/N` is nonamenable. Then for every finite symmetric
generating set `S`, with `G = Cay(Gamma,S)`,

```text
p_c(G) < p_c(N;G).
```

This is the percolation analogue of the Kesten--Grigorchuk cogrowth criterion,
which says that simple random walk returns to `N` with exponentially small
probability iff `Gamma/N` is nonamenable.

**What it would give.** Combined with `fpbs-relative-gap-along-any-subgroup-separates`,
it gives `p_c < p_u` on every Cayley graph of every group that has an infinite
normal subgroup with nonamenable quotient. That class contains:

* every nonamenable direct product `H x K` of infinite groups, taking `N = K`
  (`fpbs-product-every-generating-set`), including `T x T'` for Tarski monsters
  and `B(m,n) x B(m',n')`;
* every group with an infinite normal subgroup and non-elementary hyperbolic
  quotient (`fpbs-hyperbolic-quotient-every-generating-set`);
* every nonamenable group with an infinite amenable normal subgroup, since
  then the quotient is nonamenable.

**Evidence.**

1. **Trees.** On the free-group tree `p_c(N;T)` is the inverse cogrowth of
   `N`, and the gap holds iff `Gamma/N` is nonamenable
   (`fpbs-tree-normal-relative-threshold-is-inverse-cogrowth`).
2. **Mean field.** Slightly supercritical clusters look like critical branching
   random walk, and the projection of branching random walk with mean `m` to
   `Q = Gamma/N` visits the identity fibre finitely often in expectation iff
   `m rho(Q) < 1`. We have `rho(Q) < 1` exactly when `Q` is nonamenable, so
   near `m = 1` the fibre occupation is finite.
3. **Uniform fibres.** Below `p_c(N;G)` the cluster mass on every fibre is
   uniformly bounded (`fpbs-normal-fibre-second-moment-maximal`). In a gap
   window the infinite susceptibility is spread across infinitely many fibres,
   as branching random walk transience predicts.

**Converse direction, not claimed.** If `Gamma/N` is amenable and `N` is
nonamenable, one expects `p_c(N;G) = p_c(G)`. No proof is known, and neither
direction is used here.

## Attempts

* **BK coset-walk bound.** Split `S = S_in ∪ S_out` with `S_in = S ∩ N`. Edges
  labelled by `S_in` stay in a coset, and edges labelled by `S_out` move the
  projection to `Q = Gamma/N`. Cut an open path at its `S_out` steps and apply
  the BK inequality. With `chi_in(p)` the susceptibility of percolation on the
  fibre graph spanned by `S_in` and `mu_out` the uniform measure on the image of
  `S_out` in `Q`, this gives

  ```text
  chi^N_p <= chi_in(p) sum_n (p chi_in(p) |S_out|)^n mu_out^{*n}(e_Q),
  ```

  which is finite when `p chi_in(p) |S_out| rho(Q,mu_out) < 1`.
  **Where it dies:** the certified window has to reach above `p_c(G)`, and the
  bound gives no matching upper bound on `p_c(G)` in terms of the same
  quantities. As `p` increases, `chi_in(p)` blows up at the fibre threshold,
  while `p_c(G)` sits strictly below it. So the criterion certifies a gap only
  in product-like regimes where `S_out` dominates, and gives nothing for
  general `S`.
* **L2 threshold.** Hutchcroft's `p_c < p_{2->2}` would control `chi^N` only
  through the fibre-summed kernel
  `T^Q_p(qN, q'N) = sum_{n in N} tau_p(q, q'n)` on `l2(Q)`. For positive kernels
  the quotient norm dominates the group norm, as with Kesten's
  `rho(Gamma) <= rho(Q)`, and it strictly exceeds it in the random-walk case
  when `N` is nonamenable. **Where it dies:** boundedness of `T_p` on `l2(Gamma)`
  does not bound `T^Q_p`. For amenable `N` the two agree, and this is the
  amenable-kernel reduction already recorded in
  `fpbs-hyperbolic-quotient-every-generating-set`. For nonamenable `N`,
  bounding `T^Q_p` above `p_c` is the claim itself.
* **Uniform fibres (partial).** `fpbs-normal-fibre-second-moment-maximal`
  bounds all fibre masses by the identity fibre below `p_c(N;G)`. **Where it
  stops:** this is a consequence of the gap, not a route to it. It rules out
  single-fibre concentration in a gap window but does not create one.
* **Russo-BK integration from p_c, fibre-summed (obstruction).** Integrate
  `d tau/dp <= d T P T` upward from `p_c` and sum over `N`. By
  `fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2`, the critical
  majorant `M^N(delta)=sum_k (d delta)^k [sigma*(mu_Q*sigma)^k](e)` is finite
  for some `delta>0` iff `||S_(p_c)||_(l2(Q))<infinity`. When it is finite it
  gives the gap. But it forces `||T_(p_c)||<infinity` on `G`, which already
  gives `p_c<p_u` without the split. Under relative collapse, one
  supercritical factor makes every Picard remainder `+infinity`. **Where it
  dies:** the passage from the critical kernel to `p_c+delta`. The invariant
  is `||S_(p_c)||_(l2(Q)) >= ||T_(p_c)||`, and it is infinite for amenable
  `Q`. So Russo-BK proofs of (alpha) are at least as hard as critical l2.
* **Relative l2 threshold (reframing, 2026-09-17, swarm-0917 w5).** Define
  `p^Q_(2->2)(N;G) = sup{p : ||S_p||_(l2(Q)) < infinity}`.
  `fpbs-quotient-l2-threshold-sandwich` (ESTABLISHED) proves the following.
  - The sandwich
    `p_c <= p^Q_(2->2)(N;G) <= min{p_(2->2), p_c(N;G)}`.
  - The diagonal formula
    `||S_p|| = limsup_m (sum_(y in N) T_p^m(o,y))^(1/m)`.
  - Monotonicity in `N`, and invariance under amenable extensions `M/N`.
  - Openness, with the bound `||S_p|| >= 1/(d(p^Q_(2->2) - p))`.
  - The equivalence `p_c < p^Q_(2->2)` iff `||S_(p_c)|| < infinity`.

  This extends the Russo-BK obstruction above to every method, conditionally,
  through the open identity `fpbs-relative-threshold-is-quotient-l2-threshold`,
  `p_c(N;G) = p^Q_(2->2)(N;G)`. Unconditionally, each pair `(G,N)` falls in
  exactly one of three cases:
  - (i) critical fibre l2;
  - (ii) `p_c = p^Q_(2->2) < p_c(N;G)`;
  - (iii) no gap.

  **Where it dies:** on every pair where the weak form E' holds, a proof of
  (alpha) must bound the multi-chain critical relative susceptibilities
  `chi^(N,m)_(p_c)` exponentially in `m`, which is critical fibre l2. That
  implies `p_c < p_(2->2)` and makes the split redundant. The invariant is
  again `||S_(p_c)||_(l2(Q))`. The only escape is a type-(ii) pair: a window
  above `p_c` where `chi^N_p < infinity` but `sum_q sigma_p(q)^2 = infinity`.
  The natural test case is `F_2 x F_2` along one factor. The identity holds
  for amenable quotients and on free-group trees, and it reduces to
  `p_(2->2) = p_u` for amenable `N`.
* **Local and uniform-margin certificates (stability-approximation,
  2026-09-17, swarm-0917 w11).** The idea was to certify the gap from
  finite-radius data of `Gamma/N`, or to transplant a uniform margin through
  marked-group limits, as was done for the l2 classes.
  `fpbs-kesten-margin-collapses-near-lamplighter` (ESTABLISHED)
  tests this on the 4-regular tree. The quotients
  `Q_n = <a,t | a^2, [a, t^k a t^-k], k <= n>` are virtually free HNN
  extensions of `(Z/2)^(n+1)`, and they converge to the amenable `Z/2 wr Z`
  (their balls agree up to radius `n`). By the tree cogrowth node their
  margins are `p_c(N_n;T) - 1/3 = s(rho_n) - 1/3 > 0`, and these tend to `0`
  at rate `(2/3)(1 - rho_n)`. **Where it dies:** at the step "choose
  `delta > 0` from the radius-`R` ball of `Gamma/N`". Every ball of the
  lamplighter is shared by nonamenable `Q_n` with arbitrarily small margin.
  **Invariant:** the Kesten spectral radius `rho_Q`, which is only lower
  semicontinuous in the marked topology. Any proof must give a margin that
  vanishes as `1 - rho_Q -> 0` (linearly, on trees). So it must read a global
  quantity of the quotient walk. A quantitative law
  `p_c(N;G) - p_c(G) >= F_D(1 - rho_Q)` is not excluded.
* **Finite-models transplant, and soft supercritical inputs (transplanter,
  2026-09-19, swarm-0917 w17).** The idea was to certify `chi^N_p < infinity`
  above `p_c` on finite or approximating models, such as fibre-truncation
  towers or finite quotients `Gamma/M` with `M <= N`, and pass to the limit.
  **Where it dies:** at the limit step, for three recorded reasons.
  - Towers add no slack, and `p_u` is only lower semicontinuous along them.
  - Finite approximants carry a glued giant.
  - The margin collapses near the lamplighter (item above).

  The soft form of the limit object, a monotone invariant family equal to
  Bernoulli up to `p_c`, is killed outright by
  `fpbs-soft-collapse-kills-relative-gap-proofs` (ESTABLISHED). On every graph
  with invariant sparse spines, the collapse family has `chi^I = infinity` for
  every `t > p_c` and every infinite subgroup `I`. That class includes
  `F_2 x Z` along `Z`, `F_2 x F_2` along a factor, and `T_3 x Z` along `Z`,
  where the gap is true. **Invariant:** invariant sparse spines. **Failing
  step:** the passage from data at `p_c` to `chi^N_(p_c + delta) < infinity`.
  Any proof must use a supercritical Bernoulli property outside (S1)--(S4),
  such as BK or Russo above `p_c`, deletion tolerance, or Harris--FKG. The
  same node records a second point: submultiplicative weight tilts pulled back
  from `Q` have infinite tilted susceptibility at `p_c` on unimodular graphs,
  so Hutchcroft-type tilting needs a cocycle.

* **Radial pointwise certificates and the half-growth floor (swarm-0917 w23,
  group-rings dispatch pivoted to host-geometry).** The idea was to bound
  `chi^N_p <= sum_(n ∈ N) C e^(-a|n|)` using a radial two-point bound, which
  would give the gap for normal subgroups of relative growth `v_N < e^a`.
  The candidate rate was the half-growth rate `a = (1/2) log gr`.
  **Where it dies:** conjugation counting gives
  `v_N >= sqrt(gr) / growth(C_Gamma(n0))` for every `n0 ∈ N \ {e}`
  (`fpbs-normal-subgroup-half-growth-floor`, ESTABLISHED). Moreover
  `sum_(n ∈ N) gr^(-|n|/2) = infinity` once some `n0 ∈ N` has a centralizer of
  linear growth. So the half-growth route fails already at `p_c`, for every
  infinite normal `N` of an acylindrically hyperbolic `Gamma`.
  **Invariant:** the growth of centralizers of elements of `N`.
  What survives is essentially the product case, which tree products already
  cover. The method also stalls on two further points: the pointwise
  half-growth bound itself is unproved (Hutchcroft's bound controls only the
  worst pair `kappa`), and so is right-continuity of the rate above `p_c`.
  Radial rates close to `log gr`, as on trees, are not excluded.
