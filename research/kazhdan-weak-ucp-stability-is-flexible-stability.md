---
rg: 2
id: kazhdan-weak-ucp-stability-is-flexible-stability
kind: claim
title: For hyperlinear Kazhdan groups weak ucp-stability is full flexible HS-stability
distinct_from:
  kazhdan-subgroup-weak-ucp-exactifies-microstates: that applies the (T)-averaging to a Kazhdan SUBGROUP C of a host A and only exactifies one selected microstate sequence on C, leaving the host inexact; this uses tensor regularization plus (T)-rounding to correct every asymptotic representation of a hyperlinear Kazhdan group.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that is the Becker--Lubotzky no-go for STRICT (same-dimension) HS-stability of infinite hyperlinear Kazhdan groups; this is a positive equivalence between two FLEXIBLE-type notions (weak ucp, flexible) for Kazhdan groups and says nothing about strict stability.
  sln-z-flexibly-hs-stable: that is the open positive hypothesis for some integral lattice; this is the general equivalence showing that, once the Kazhdan group is hyperlinear, Dogon's formally weaker weak ucp-stability already implies full flexible stability on all asymptotic representations.
---

**THEOREM.**  Let `Gamma` be a finitely generated **hyperlinear** group with
Kazhdan's property (T).  The following are equivalent:

```text
(a) Gamma is weakly ucp-stable (Dogon arXiv:2211.10492 Def 1.5): every
    hyperlinear approximation phi_n : Gamma -> U(d_n) satisfies
    || phi_n(g) - P_n pi_n(g) P_n ||_(2,d_n) -> 0 for genuine unitary
    representations pi_n on Hilbert spaces H^_n supseteq C^(d_n), finite
    or infinite dimensional;
(b) Gamma is flexibly HS-stable (Dogon Def 1.2 / Dogon--Vigdorovich Def
    1.2): every asymptotic representation alpha_n, separating or not,
    satisfies || alpha_n(g) - P_n pi_n(g) P_n ||_(2,d_n) -> 0 for genuine
    FINITE-dimensional representations pi_n on C^(D_n) supseteq C^(d_n),
    D_n / d_n -> 1.                                                   (WF1)
```

`(b) => (a)` is immediate.  For `(a) => (b)`, first apply weak ucp-stability
and property `(T)` to one separating hyperlinear approximation.  Kazhdan
averaging of its Stinespring corner gives genuine finite-dimensional
representations whose normalized characters still converge to `delta_e`.
For an arbitrary asymptotic representation `alpha_n`, tensor with that exact
regular family.  The tensor product is hyperlinear, so `(a)` supplies a ucp
correction.  The constant-one maximally-entangled recovery in
`residual-finite-regularization-removes-the-weak-ucp-quantifier` untensors it
to a ucp correction of `alpha_n`.  A second Kazhdan averaging turns its
Stinespring corner into a finite-dimensional genuine correction of relative
dimension `1+o(1)`.  Dogon's Prop. 1.11 is the residual-finiteness corollary
obtained by combining this full flexible stability with Becker--Lubotzky.

**Consequences recorded in the graph.**

- `sl3-z-weakly-ucp-stable` is exactly the `n = 3` full-flexible instance
  of `sln-z-flexibly-hs-stable`.  Residual finiteness supplies the exact
  regular tensor packets directly, and property `(T)` removes the ucp
  dilation.  Neither infinite-dimensional dilations nor the separating
  input quantifier weakens the problem for this lattice.
- The HNN theorem `hnn-over-codense-kazhdan-subgroup-not-hyperlinear`
  applies stability only to the microstate sequence of the HNN group
  restricted to the host, which is a hyperlinear approximation of the
  host; so for Kazhdan hosts its hypothesis may be stated as weak
  ucp-stability.  Route `non-hyperlinear-from-sl3-z-weak-ucp-stability`.
- The subgroup exactification
  `kazhdan-subgroup-weak-ucp-exactifies-microstates` is the relative form
  of the same averaging; when the Kazhdan subgroup itself admits a thin
  co-dense `(tau)` pair (as `SL_n(Z)`, `n >= 3`, does by
  `sln-z-thin-codense-tau-pair`), the direct route through this lemma
  supersedes the face-confinement it provides.

**Remark on Dogon's Theorem 1.6 (superseding the earlier quantifier
remark).**  Every group to which Dogon's
Theorems 1.3/1.6 and Corollaries 1.8--1.9 apply has property (T)
(`Sp_(2g)(Z)`, Gromov random groups at density in `(1/3, 1/2)`, infinitely
presented Kazhdan groups).  Source check (arXiv HTML of 2211.10492,
2026-08-21): Definition 1.2 (flexible HS-stability) quantifies over ALL
asymptotic homomorphisms, while Definition 1.5 (weak ucp-stability)
quantifies ONLY over hyperlinear approximations (Definition 1.4:
`liminf || phi_n(g) - 1 ||_2 >= sqrt 2` for `g != e`).  Those definitions
alone only give a restricted-quantifier statement.  The later
tensor-regularization argument
`residual-finite-regularization-removes-the-weak-ucp-quantifier` removes
that restriction for **hyperlinear** Kazhdan groups: first round one
separating approximation to an exact regular finite-dimensional family,
then use it to regularize and contractively recover every other asymptotic
representation.  Thus the earlier claim that the class restriction remains
real for Kazhdan groups is superseded.  Hyperlinearity is load-bearing;
without any separating approximation weak ucp-stability can be vacuous.

**Literature cousin.**  Fournier-Facio--Willett arXiv:2603.18456v2,
Theorem 1.1: if `C^*(Gamma)` has the LLP and is RFD then every asymptotic
representation (operator, Hilbert--Schmidt or Schatten norm) is near
corners of genuine FINITE-dimensional representations ("very flexibly
stable"); there RFD supplies the finite-dimensional reduction.  Here
property (T) supplies it instead, which is the relevant replacement for
Kazhdan groups, where RFD typically fails (Bekka for `SL_n(Z)`, `n >= 3`;
their Question 1.10 asks whether any infinite Kazhdan group is RFD).

**Boundary.**  The lemma needs hyperlinearity to obtain the first separating
packet and full property `(T)` to round both Stinespring corners (the
dilation spaces may be infinite dimensional, so `(T;FD)` does not reach
them).  For a non-hyperlinear Kazhdan group the weak-ucp quantifier can be
empty, and no implication to full flexible stability follows.
