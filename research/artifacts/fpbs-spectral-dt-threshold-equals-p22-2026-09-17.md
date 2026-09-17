# The spectral DT threshold is the L2 threshold

September 17, 2026 (swarm-0917, worker w5-bs-critical-l2, role inverter).
Target hole: `fpbs-nonamenability-bounds-critical-connectivity-operator`.
Nothing here is refereed or formally verified.

## 0. Summary

`research/artifacts/fpbs-spectral-dt-certificate-2026-09-17.md` (Section 3.3)
defines, on `G = Cay(Gamma, D)`,

```text
nu_{S,p}(g) = p * sum_{ {u,v} in Delta S, v = g } P_p(o <->_S u),
p_sDT(G)    = sup{ p : some finite S containing o has sp(rho_Gamma(nu_{S,p})) < 1 },
```

and proves `p_c <= p_sDT <= p_{2->2}`. Its Section 7 leaves open the converse:
is `p_sDT = p_{2->2}`? This note settles it.

* **Theorem 1.** `p_sDT(G) = p_{2->2}(G)` on every Cayley graph. Quantitatively,
  if `N_p = ||T_p||_{2->2} < infinity`, then for every `R >= 0`
  ```text
  sp(rho_Gamma(nu_{B_R,p})) <= ||rho_Gamma(nu_{B_R,p})|| <= p |D| e N_p exp(-R/(e N_p)),
  ```
  so the ball `B_R` is a certificate as soon as `R > e N_p log(e p |D| N_p)`.
* **Corollary 2 (finite-volume form of the conjecture).** On `G` the following
  are equivalent:
  1. `||T_{p_c}||_{2->2} < infinity`;
  2. `p_c < p_{2->2}`;
  3. some finite `S` containing `o` has `sp(rho_Gamma(nu_{S,p_c})) < 1`;
  4. some ball has `||rho_Gamma(nu_{B_R,p_c})||_{2->2} < 1`.

  At `p_c` every such measure has total mass `phi_{p_c}(S) >= 1`
  (Duminil-Copin–Tassion). So Hutchcroft's conjecture says exactly this: at
  criticality, the DT boundary measure of some ball has mass at least one but
  convolution norm below one.
* **Corollary 3 (a prerequisite collapses).**
  `fpbs-wq-normal-class-critical-spectral-dt-certificate` is equivalent, graph
  by graph, to `p_c < p_{2->2}` on its class. Its first recorded failure mode
  ("fail on a graph with `p_c < p_{2->2}` if `p_sDT < p_{2->2}`") cannot occur.
  The open need "a critical certificate on `F_2 x Z`" is exactly the L2
  conjecture on that graph.

The proof is short. It composes two established results: the finite-volume
certificate framework, and the tail bootstrap of
`fpbs-sphere-fibre-operator-iff-critical-fibre-l2` with trivial kernel `H = {1}`.
That bootstrap is Hutchcroft's arXiv:1904.05804, Proposition 2.4. The artifact
Section 7 observed that the naive bound needs the sphere operator to be *small*.
The bootstrap supplies exactly that smallness, because tail operator norms decay
exponentially.

## 1. Setting and inputs

`Gamma` is finitely generated, `D` a finite symmetric generating set counted with
multiplicity, and `G = Cay(Gamma, D)` has edges `{x, xs}`. `|x|` is word length
from `D`, `B_R = {|x| <= R}`, `S_R = {|x| = R}`. `tau_p(x,y) = P_p(x <-> y)`,
`sigma_p(g) = tau_p(o,g)`, and `T_p` has kernel `tau_p`. For a finitely supported
or nonnegative `f` on `Gamma`,

```text
(rho(f) phi)(x) = sum_g f(g) phi(xg),     N(f) = ||lambda_Gamma(f)||_{2->2} in [0, infinity],
(f * g)(x)      = sum_y f(y) g(y^(-1) x),  C_{p,r} = sigma_p 1_{|.| >= r}.
```

The inputs are:

* **(I1) Certificate framework.** Artifact
  `research/artifacts/fpbs-spectral-dt-certificate-2026-09-17.md`
  (node `fpbs-spectral-dt-certificate-bounds-connectivity-operator`, ESTABLISHED).
  * Section 1: `rho(f) rho(f') = rho(f * f')`, and `rho` is unitarily equivalent
    to `lambda_Gamma` via `phi -> phi(.^(-1))`, so `||rho(f)|| = N(f)`.
  * Theorem A and Corollary 3.1: if `sp(rho(nu_{S,p})) < 1`, then
    `||T_p|| < infinity`, and the certificate set of `p` is `(0, p_S)`.
  * Section 3.3: `p_c <= p_sDT <= p_{2->2}`.
* **(I2) Positive kernels.** For `f, g >= 0`: `N(f * g) <= N(f) N(g)`; if
  `f <= g` entrywise then `N(f) <= N(g)`; and `N(f) <= ||f||_1`. This is (F2) of
  `research/artifacts/fpbs/docs/sphere-fibre-operator-is-critical-l2.md`.
* **(I3) Tail bootstrap.** Theorem A, "(b) implies (c)", of the same artifact
  (node `fpbs-sphere-fibre-operator-iff-critical-fibre-l2`, ESTABLISHED), with
  the normal subgroup `H = {1}`, so `Q = Gamma` and the fibre sum
  `sigma_p(q) = tau_p(o,q)`. The artifact states that the proof "works at any `p`
  with `N_p := N(sigma_p) < infinity`". It uses only the sphere cut (F1), which
  holds for every `p`, and (I2). Its conclusion is
  ```text
  N(C_{p,r}) <= e N_p exp(-r/(e N_p))    for all r >= 0.
  ```
  This is the fibre version of arXiv:1904.05804, Proposition 2.4. With `H = {1}`
  it is that proposition itself, proved in the artifact.
* **(I4) Kernel identity.** `T_p = rho(sigma_p)`. Indeed
  `(rho(sigma_p) phi)(x) = sum_y tau_p(o, x^(-1) y) phi(y) = sum_y tau_p(x,y) phi(y)`
  by left invariance. So `||T_p|| = N(sigma_p) = N_p`, the `H = {1}` case of (F4)
  in the sphere-fibre artifact.
* **(I5) Openness of the L2 phase.** Hutchcroft arXiv:1804.10191 (cited as (F5)
  in the sphere-fibre artifact): `||T_{p_{2->2}}|| = infinity`, so
  `||T_{p_c}|| < infinity` iff `p_c < p_{2->2}`.
* **(I6) DT at criticality (remark only).** Duminil-Copin–Tassion
  arXiv:1502.03050, imported verbatim in
  `research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md` Section 1:
  `p_c = sup{p : phi_p(S) < 1 for some finite S containing o}`. This is used only
  in the mass remark of Corollary 2.

## 2. Theorem 1

**Theorem 1.** Let `p` be in `(0,1)` with `N_p = ||T_p|| < infinity`. For every
`R >= 0`,

```text
sp(rho(nu_{B_R,p})) <= ||rho(nu_{B_R,p})|| <= p |D| e N_p exp(-R/(e N_p)).
```

Consequently `p_sDT(G) = p_{2->2}(G)`.

*Proof.*

1. **The boundary measure sits on one sphere.** An edge `{u,v}` of `Delta B_R`
   has `|u| <= R < |v|`. Since `v = us` with `s in D`, `|v| <= |u| + 1`, so
   `|u| = R`. Also `P_p(o <->_{B_R} u) <= tau_p(o,u)`. Put
   `f = sigma_p 1_{S_R}` and `a = sum_{s in D} delta_s`. For every `g`,
   ```text
   nu_{B_R,p}(g) <= p sum_{s in D} f(g s^(-1)) = p (f * a)(g).
   ```
2. **Norm of the boundary measure.** By (I1) and (I2),
   `||rho(nu_{B_R,p})|| = N(nu_{B_R,p}) <= p N(f) N(a) <= p |D| N(f)`, using
   `N(a) <= ||a||_1 = |D|`.
3. **Smallness from the bootstrap.** `f <= C_{p,R}` entrywise. So (I2), (I3)
   and (I4) give `N(f) <= N(C_{p,R}) <= e N_p exp(-R/(e N_p))`.
4. **Spectral radius.** `sp(a) <= ||a||` for every bounded operator. This proves
   the displayed bound.
5. **Thresholds.** Let `p < p_{2->2}`. Then `N_p < infinity`, since `tau_p` is
   nondecreasing in `p` and (I2) applies. Choose `R > e N_p log(e p |D| N_p)`.
   The bound is then below 1, so `B_R` certifies at `p` and `p_sDT >= p`. Hence
   `p_sDT >= p_{2->2}`. The reverse inequality is (I1), Section 3.3. QED.

**Remarks.**

* The certifying radius is at most `e N_p log(e p |D| N_p) + 1`, which is
  explicit in `||T_p||` alone.
* Balls always suffice. The norm itself falls below one, not only the spectral
  radius.
* The proof uses no hyperbolicity, no rapid decay and no nonamenability. On an
  amenable group `||T_p|| = chi_p`, so `p_c = p_sDT = p_{2->2}`, which agrees
  with the certificate artifact, Section 6.2.

## 3. Corollaries

**Corollary 2.** On every Cayley graph `G = Cay(Gamma, D)` the following are
equivalent:

1. `||T_{p_c}|| < infinity`;
2. `p_c < p_{2->2}`;
3. some finite `S` containing `o` has `sp(rho(nu_{S,p_c})) < 1`;
4. some `R` has `||rho(nu_{B_R,p_c})|| < 1`.

At `p = p_c`, every finite `S` has `phi_{p_c}(S) = nu_{S,p_c}(Gamma) >= 1`.

*Proof.* (1) iff (2) is (I5). (1) implies (4) is Theorem 1 at `p = p_c`.
(4) implies (3) because `sp <= ||.||`. (3) implies (2) is (I1), Corollary 3.3.
For the mass statement: `phi_p(S)` is a polynomial in `p`. If
`phi_{p_c}(S) < 1`, then `phi_p(S) < 1` for some `p > p_c`, which contradicts
(I6). QED.

**Corollary 3 (zero-one law for critical ball norms).** Put
`b_R = ||rho(nu_{B_R,p_c})||`. Exactly one of the following holds:

* **(i)** `b_R <= p_c |D| e N exp(-R/(e N))` for all `R`, where
  `N = ||T_{p_c}|| < infinity`;
* **(ii)** `sp(rho(nu_{S,p_c})) >= 1` for every finite `S`, so in particular
  `b_R >= 1` for all `R`.

No intermediate behaviour occurs. For instance, `b_R -> 1/2` is impossible, and
so is `b_R` bounded away from 0 but eventually below 1.

*Proof.* If some `S` has `sp < 1`, Corollary 2 gives `N < infinity`, and
Theorem 1 gives (i). Otherwise (ii) holds. Both cannot hold, since (i) forces
`b_R < 1` for large `R`. QED.

**Corollary 4 (collapse of recorded prerequisites).**

1. `fpbs-wq-normal-class-critical-spectral-dt-certificate` (OPEN) is equivalent,
   graph by graph, to `p_c < p_{2->2}` on its class. Its first recorded failure
   mode, "`p_c < p_{2->2}` but `p_sDT < p_{2->2}`", cannot occur. The bounty-4
   need for a critical certificate on `F_2 x Z` is exactly the L2 conjecture on
   that Cayley graph.
2. With Part 3 of `fpbs-direct-limit-certificates-add-no-slack`: on a direct
   limit `Gamma` of marked groups `H_i`, `p_c(Gamma) < p_{2->2}(Gamma)` iff one
   finite datum `(S, p > p_c(Gamma), n, c < 1)` certifies infinitely many
   approximants.

## 4. What this does to the target

* **The finite-volume hierarchy is lossless.** The spectral DT certificates are
  an exact characterisation of the L2 gap, not only a sufficient condition.
  Every graph with `p_c < p_{2->2}` (hyperbolic, nonunimodular, acylindrically
  hyperbolic, free products, `T_k x Z^m`) has a ball certificate at `p_c` with
  radius `O(N log N)`, where `N = ||T_{p_c}||`. So no class kill of spectral
  certificates can reach a graph where the conjecture is true. A proof that
  certificates fail on a graph is a proof that the conjecture fails there.
* **Hutchcroft's conjecture as a mass-versus-norm gap.** At `p_c`, the explicit
  finitely supported measure `nu_{B_R,p_c}` has mass at least 1 for every `R`.
  The conjecture says its convolution norm is below 1 for some `R`, and then it
  tends to 0 exponentially. This is a Kesten-type statement about one explicit
  family of measures, and it is where nonamenability must enter. On amenable
  groups, norm equals mass for nonnegative measures.
* **Minimal counterexample shape.** A counterexample is a Cayley graph where
  every critical ball boundary measure, including every power, has
  `||rho(nu_{B_R,p_c}^{*n})|| >= 1`, since the spectral radius is at most
  `||a^n||^(1/n)`. By Corollary 3 there is no "slowly failing" regime. If the
  norms at one radius dip below 1, they are exponentially small at every large
  radius.
* **What it does not do.** It proves nothing about which graphs satisfy the
  conjecture. It converts every open certificate need in the graph into the
  conjecture itself, which prevents recording those needs as easier
  prerequisites.

## 5. Caveats

* Prior art: Hutchcroft's Proposition 2.4 already gives exponential decay of
  tail operator norms. The combination with DT finite-volume exploration may
  be implicit in the literature. The search (`bin/cairn search`, 2026-09-17)
  found no node stating `p_sDT = p_{2->2}`, and the certificate artifact lists
  it as open.
* Quasi-transitive or non-Cayley transitive graphs are not treated, because the
  certificate framework is stated for Cayley graphs.
