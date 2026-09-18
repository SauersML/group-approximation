---
rg: 2
id: fpbs-two-point-state-axioms-admit-collapse
kind: claim
title: On every nonamenable Cayley graph a Harris-supermultiplicative positive-definite state family equal to Bernoulli through p_c has uniqueness-type atoms at every p above p_c
distinct_from:
  fpbs-uniqueness-spectrum-critical-remainder: that works with abstract walk-sampling measures (two-atom measures with vanishing total-variation error); this realises the jump as functions on the group itself, with positive definiteness, Harris supermultiplicativity, the exact critical state and the exact theta, on every nonamenable Cayley graph
  fpbs-soft-collapse-iff-invariant-sparse-spines: that is an event-level collapse family, it exists only where invariant sparse spines exist (not on F_2), and Harris-FKG is undecided there; this is state-level, exists on every nonamenable Cayley graph including F_2 and Kazhdan groups, and is Harris-supermultiplicative
  fpbs-finite-energy-fkg-collapse-over-central-z2-slabs: that is an event-level FKG collapse needing a central Z inside a Z2; this is a two-point state family on every nonamenable Cayley graph
  fpbs-bk-majorant-integrated-sensitivity-is-critical-l2: that shows the Russo-BK series has zero radius when the critical operator is unbounded, and proves Hutchcroft's majorant on graphs where it is bounded; this shows that on those graphs the majorant cannot be derived from infinite-volume state facts, so its truncation step is load-bearing
  fpbs-uniqueness-spectral-atom-decomposition: that decomposes Bernoulli walk connectivity at one uniqueness parameter; this uses that decomposition as an axiom and builds a non-Bernoulli family satisfying it at every parameter above p_c
  fpbs-kazhdan-uniform-walk-decorrelation: that proves NC and VIS are equivalent to p_c<p_u on Kazhdan graphs; this shows its uniform decorrelation bound, together with the other state axioms, is consistent with collapse
---

**ESTABLISHED (class-killing obstruction, state level).** Proof in
`fpbs-two-point-state-axioms-admit-collapse-proof`.

**Setting.** `Gamma` is a finitely generated nonamenable group, `S` a finite
symmetric generating set with `|S| = d`, and `G = Cay(Gamma,S)`. Write
`mu_S` for the simple step law and `mu_L = (delta_e + mu_S)/2` for the lazy
one. Let `rho = ||lambda(mu_S)||` and `rho_L = ||lambda(mu_L)|| = (1+rho)/2`,
both below one. Let `tau_p(x) = P_p(e <-> x)`, let `theta(p)` be the
percolation density, and let `u(p) = 1{U_p}` be the uniqueness indicator.

**Two-point state family.** This is a family `g = (g_p)_(p in [0,1])` of
functions `Gamma -> [0,1]`. For each `g_p` put
`a^L_n(g_p) = sum_x mu_L^(*n)(x) g_p(x)`,
`a_n(g_p) = sum_x mu_S^(*n)(x) g_p(x)`,
`lambda(g_p) = limsup a_n^(1/n)`,
`A(g_p) = sum_n a_n(g_p)`, and let `G_p` be the kernel
`G_p(x,y) = g_p(x^(-1)y)`. The axioms are:

* **(T1) positivity.** `g_p` is positive definite, `g_p(e) = 1`, and
  `g_p(x^(-1)) = g_p(x)`.
* **(T2) mixed Harris.** `g_p(xy) >= g_p(x) g_q(y)` for all `q <= p`.
* **(T3) monotonicity.** `g_q <= g_p` pointwise for `q <= p`.
* **(T4) critical agreement.** `g_p = tau_p` for every `p <= p_c`.
* **(T5) atom plus remainder.**
  `a^L_n(g_p) = theta(p)^2 u + int_[0,1) t^n d nu_p(t)`. Here `u` is in
  `{0,1}` and nondecreasing in `p`, and `nu_p >= 0` has mass
  `1 - theta(p)^2 u`. When `u = 1`, `nu_p` is supported in `[0, rho_L]`.
* **(T6) Kazhdan decorrelation.** If `kappa(Gamma,S) > 0` and
  `eta = 1 - kappa^2/(4d)`, then
  `a^L_n(g_p) <= theta^2 u + (1 - theta^2 u) eta^n`.
* **(T7) right weak* continuity at `p_c`.** `g_p -> g_(p_c)` pointwise as
  `p` decreases to `p_c`.
* **(T8) integrated infinite-volume Russo–BK.** For `q < p` and all `x`,
  `g_p(x) - g_q(x) <= d int_q^p (G_s P G_s)(e,x) ds`, with values in
  `[0, infinity]`. Here `P` is the simple random walk kernel.

**Theorem.**

1. *(Bernoulli is a model.)* Bernoulli percolation `g_p = tau_p`, with
   `u = u(p)`, satisfies (T1)–(T8).
2. *(Collapse witness.)* Define
   `f_p = tau_p` for `p <= p_c`, and
   `f_p = theta(p)^2 + (1 - theta(p)^2) tau_(p_c)` for `p > p_c`,
   with `u = 1{p > p_c}`. Then `f` satisfies (T1)–(T8). For every `p > p_c`:
   * `lim_n a^L_n(f_p) = theta(p)^2 > 0`;
   * `lambda(f_p) = 1` and `A(f_p) = infinity`;
   * `||G_p||_(2->2) = infinity`;
   * the walk spectral measure is `theta(p)^2 delta_1 + (1-theta(p)^2) nu_(p_c)`,
     where `nu_(p_c)` is supported in `[0, rho_L]`.

   The key inequality behind (T2) is the convexity lemma. If `0 <= t <= 1`
   and `t(xy) >= t(x)t(y)`, then `a + (1-a)t` is supermultiplicative for
   every `a in [0,1]`, with defect at least `a(1-a)(1-t(x))(1-t(y))`.
3. *(Truncation is load-bearing.)* Suppose `||T_(p_c)||_(2->2) < infinity`.
   This holds on every Cayley graph with `p_c < p_(2->2)`, including every
   acylindrically hyperbolic group and so `F_2`. Then `f` admits no
   *truncation system*. A truncation system is a set of finite kernels
   `tau^R_p` on `B_R` that are continuously differentiable in `p`, increase
   in `R` to `f_p`,
   satisfy (4.1) of `fpbs-bk-majorant-integrated-sensitivity-is-critical-l2-proof`,
   and have `tau^R_(p_c) <= f_(p_c)`. Bernoulli has one, and Bernoulli
   satisfies `a_n(p_c+delta) <= M rho^n/(1-d delta M)`.

**What this kills.** Call the *two-point state class* the arguments whose
inputs about the family `p -> tau_p` are (T1)–(T8). This includes:

* every weak*-continuous group-ring or C*-functional of the states;
* Harris supermultiplicativity;
* the GNS and Fell-absorption description of the cluster representation;
* the Kazhdan projection bound;
* the infinite-volume Russo–BK integral.

On **every** nonamenable Cayley graph, no argument in this class can prove any
of the following:

* nonuniqueness at some `p > p_c`, and hence `p_c < p_u`;
* NC (`lambda < 1` above `p_c`);
* VIS (`A < infinity` above `p_c`);
* the continuation `||T_(p_c)|| < infinity => ||T_p|| < infinity` for some
  `p > p_c`;
* any exponential walk-decay bound above `p_c`.

Such an argument would apply verbatim to `f`. PB, IS and GB imply NC or VIS
(`research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`,
`fpbs-green-visit-kernel-ordering`), so the class cannot prove
`fpbs-pivotal-budget-universal` either.

* **Invariants.** The atom `m(g_p) = lim a^L_n = inf_n a^L_n` and the
  top-of-spectrum rate `lambda(g_p)`. The quantities `A(g_p)` and
  `||G_p||_(2->2)` are also invariants.
* **Failing step.** The continuation from `p_c` to `p_c + eps`.
  * The only link that (T1)–(T8) supply between the critical state and
    supercritical states is (T3), (T7) and the infinite-volume integral (T8).
  * The atom is an infimum of weak*-continuous functionals, hence upper
    semicontinuous. (T7) therefore forces only `m(g_p) -> 0`, which is
    `theta(p_c+) = 0`, already known from BLPS.
  * The rate, `A` and the operator norm are suprema or tops of support. They
    are only lower semicontinuous, and `f` makes them jump from
    `lambda(p_c) <= rho`, `A(p_c) <= 1/(1-rho)` and `M` to one or `+infinity`.
  * (T8) is vacuous there: the integrand `G_s P G_s` is `+infinity` as soon
    as `theta(s) > 0`.

**Calibration.**

* On acylindrically hyperbolic graphs Bernoulli has `lambda < 1` just above
  `p_c`, while `f` agrees with Bernoulli on `[0,p_c]` and does not. By
  part 3, the step of Hutchcroft's mechanism that passes to the finite
  polynomial kernels of (4b)–(4e) is exactly where state information stops.
  This confirms, at the level of axioms, Section 6 of the pivotal-kernel
  ordering: a universal proof must control finite-radius events uniformly in
  `R`.
* On `F_2` no event-level soft collapse exists, by cost. `f` exists
  nonetheless, so cost-type obstructions are invisible to two-point states.
* On Kazhdan graphs `f` satisfies (T6). The uniform decorrelation of
  `fpbs-kazhdan-uniform-walk-decorrelation` therefore cannot be upgraded to
  `p_c < p_u` by state-level reasoning.

**Not claimed.**

* `f` is not asserted to be the two-point function of any invariant
  percolation.
* It is not decided whether some family satisfies (T1)–(T8) and admits a
  truncation system while collapsing, on a graph with
  `||T_(p_c)|| = infinity`.
* Arguments that use events (pivotal counts in finite balls, cluster
  geometry, realisability, cost) are outside the class and are not killed.
