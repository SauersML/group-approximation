---
rg: 2
id: fpbs-continuous-activation-collapse-family
kind: claim
title: Collapse families whose spine edges switch on one at a time at continuously distributed times have absolutely continuous annealed kernels, so the operator gate fails in its density term and never needs jump atoms
distinct_from:
  fpbs-quenched-bk-russo-collapse-operator-gate: that family switches a whole infinite spine level on at one deterministic parameter, so its annealed kernels jump and it leaves open whether the interval estimate (a) or the jump estimate (b) fails; here no deterministic jump time exists, every quenched jump is a single edge of weight at most one, and (G) fails with the atom part vacuous
  fpbs-sharp-dominating-collapse-over-sparse-spines: same spines and the same properties (S1)-(S4), (H1)-(H5); this replaces the step schedule n(t) by a continuum of nested connected spines interpolated through geodesic forests
  fpbs-fiid-uniform-finite-energy-fkg-collapse-family: that family targets FIID, finite energy and FKG; this targets the time regularity of annealed connection kernels
---

**ESTABLISHED (class-killing obstruction).** Proof in
`fpbs-continuous-activation-collapse-family-proof`.

**Setting.** As in `fpbs-quenched-bk-russo-collapse-operator-gate`. `G = Cay(Gamma,S)`
is a Cayley graph of a nonamenable group, `d = |S|`, `J` is the adjacency
matrix, and `xi_t = {e : U_e <= t}`. For finite `Lambda`,
`T^Lambda_t(u,v) = P(u <-> v in omega_t ∩ Lambda)`, with `T^Lambda_t(u,u) = 1`.
`G` has invariant sparse spines.

**Theorem 1 (continuous-activation collapse family).** Fix any `f`, `R` as in
`fpbs-sharp-dominating-collapse-over-sparse-spines`. There is an ergodic
system carrying `U` and a family

```text
omega_t = xi_t               (t <= p_c),
omega_t = xi_t ∪ Z_t         (t >  p_c),     Z_t = {e : tau_e <= t},
```

with the following properties. The environment `M` is everything except `U`.
It is independent of `U`, and the activation times `tau_e in (p_c, infinity]`
are `M`-measurable.

* **(C0)** (S1)-(S4) and (H1)-(H5) of the sharp dominating family hold
  verbatim. In particular `omega_t` has exactly one infinite cluster for
  every `t > p_c`, `T_t >= theta_xi(t)^2` entrywise, and the density of `Z_t`
  is at most `3 · 2^-n(t) <= f(t)`.
* **(C1) Quenched product.** Given `M`, the edge processes are independent,
  with `omega_t(e) = 1{U_e <= p_e(t)}`, where `p_e(t) = 1` if
  `t >= tau_e` and `p_e(t) = t` otherwise. So the quenched law satisfies
  Harris-FKG and BK-Reimer and dominates `P_t`.
* **(C2) Single-edge quenched jumps.** Almost surely all finite activation
  times are distinct. For finite `Lambda`, `tau^{M,Lambda}_t` is a polynomial
  in `t` between the finitely many activation times in `Lambda`, and there
  `d/dt tau^{M,Lambda} <= tau^{M,Lambda} J tau^{M,Lambda}`. At `r = tau_e`,
  with `e = {a,b}`, the jump is

  ```text
  tau^{M,Lambda}_{r+} - tau^{M,Lambda}_{r-} <= (1-r) tau^{M,Lambda}_{r-} J_e tau^{M,Lambda}_{r-},
  ```

  where `J_e` is the adjacency matrix of the single edge `e`. So every quenched
  jump has weight at most `1` and a kernel of norm `1`.
* **(C3) No annealed jumps.** For every edge `e`, `t -> P(tau_e <= t)` is
  absolutely continuous on `[p_c,1]`. Its density `rho_e` satisfies
  `∫_{p_c}^t rho_e = P(e in Z_t) <= 3 · 2^-n(t)`. For every event `E`
  determined by a finite edge set `F_E`, `t -> P(omega_t in E)` is absolutely
  continuous on `[0,1]`, and
  `|d/dt P(omega_t in E)| <= sum_{e in F_E} (1 + rho_e(t))` a.e. Hence every
  `T^Lambda_t` is entrywise absolutely continuous, including at `p_c`, and
  `P(omega_t ∩ Lambda ≠ omega_{t-} ∩ Lambda) = 0` for every `t`.
* **(C4)** Exact annealed independent sprinkling, and **(C5)** local annealed
  BK at range `R(t)` with error `f(t)`, as (Q4)-(Q5) of the operator gate.

**Theorem 2 (the gate fails in the density term).** Suppose in addition that
`||T_{p_c}||_{2->2} < infinity`, as on closed hyperbolic mapping tori of
pseudo-Anosov maps. Choose Borel versions of the a.e. derivatives
`dT^Lambda_r/dr` and put

```text
C*(r)       = sup over finite Lambda and u,v of  (dT^Lambda_r/dr)(u,v) / (T^Lambda_r J T^Lambda_r)(u,v),
C_Lambda(r) = the same supremum over u,v for one fixed Lambda,
```

with `0/0 = 0` and `x/0 = infinity` for `x > 0`. Then:

1. `∫_{p_c}^{p_c+eps} C*(r) dr = infinity` for every `eps > 0`. So no
   integrable `C` gives `dT^Lambda/dr <= C T^Lambda J T^Lambda` uniformly in
   `Lambda`.
2. For each fixed `Lambda`,
   `C_Lambda(r) <= p_c^{-|Lambda|} sum_{e in Lambda} (1 + rho_e(r))` a.e., which is
   integrable on `[p_c,1]`.
3. (G) of `fpbs-quenched-bk-russo-collapse-operator-gate` fails on every
   `[p_c,p_c+eps]`, for every integrable `C` and every summable atoms.
   The family has no annealed jump times, so in the dichotomy of Corollary 3
   there the jump estimate (b) is vacuous. The failure is carried entirely by
   the density estimate.

**Proposition 3 (quenched jumps are forced).** Let `(omega_t)` be any
invariant family of the form `omega_t = {e : U_e <= p^M_e(t)}` with `M`
independent of `U` and `p^M_e(t) >= t`. If `omega_t` has a unique infinite
cluster a.s. for some `t > p_c`, then `sup_e p^M_e(t) >= p_u` a.s. On a graph with
`p_c < p_u`, every such collapse family therefore raises some quenched edge
densities by at least `p_u - p_c` immediately after `p_c`. This step is
elementary.

**Answer to the (a)/(b) question.** The question comes from
`fpbs-quenched-bk-russo-collapse-operator-gate`. Jump atoms are not
load-bearing. A macroscopic quenched jump is unavoidable (Proposition 3), but
each such jump can be placed on a single edge at a continuously distributed
time. Annealing then turns the jumps into an integrable density (C3). The
obstruction survives unchanged, and (G) now fails in its density term.
Calling (a) and (b) separate estimates is therefore not intrinsic:
smearing moves mass from (b) into the density term. The intrinsic failing
statement is the uniform-in-volume density bound 1.

**Exact failing step.** The failure is non-equicontinuity in the volume. Each
`g_Lambda(t) = ||T^Lambda_t||` is continuous on `[p_c,1]` with
`g_Lambda(p_c) <= ||T_{p_c}||`, and its density ratio `C_Lambda` is
integrable. But `sup_Lambda g_Lambda(t) = ||T_t|| = infinity` for every
`t > p_c`, and `sup_Lambda C_Lambda` is not integrable at `p_c`. The per-edge
activation mass `∫ rho_e` tends to `0`. So the failure is not an excess of
activation. It is the amplification of rare activations by the
environment-correlated quenched two-point functions
`tau^M(u,a) tau^M(b,v)`, which annealing cannot factor into `T(u,a) T(b,v)`
at a rate that is integrable uniformly in `Lambda`.

**Class killed.** Suppose an argument proves `p_c < p_u` on the critical-L2
spine graphs using only these inputs above `p_c`:

* the inputs of the sharp dominating corollary;
* Harris-FKG, BK-Reimer and Russo applied conditionally on an environment
  independent of the labels, with single-edge quenched jumps of weight at
  most one;
* absolute continuity in `t` of every local annealed probability, with
  integrable per-edge rates whose total mass is at most `f(t)`;
* the absence of any deterministic jump time;
* exact independent sprinkling;
* local BK.

Then the argument proves a false statement. Together with the jump family of
the operator gate, this also kills arguments that use either exact annealed
Russo off a countable set, or annealed absolute continuity.

**Next step.** Split the density `dT^Lambda/dr = R_r + A_r`. Here `R_r` is the
annealed off-spine pivotal term, and `A_r` is the activation term, whose
per-edge rate is integrable with vanishing mass. Decide whether `R_r` alone
satisfies `R_r <= C(r) T J T` with `C` integrable uniformly in `Lambda`, which
is an annealed pivotal factorization. If it does, the gate reduces to
controlling the activation amplification `A_r`.
