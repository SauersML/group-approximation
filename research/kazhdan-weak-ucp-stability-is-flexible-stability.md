---
rg: 2
id: kazhdan-weak-ucp-stability-is-flexible-stability
kind: claim
title: For Kazhdan groups weak ucp-stability is flexible HS-stability on hyperlinear approximations
distinct_from:
  kazhdan-subgroup-weak-ucp-exactifies-microstates: that applies the (T)-averaging to a Kazhdan SUBGROUP C of a host A and only exactifies the microstates on C, leaving the host inexact; this applies it to the Kazhdan group ITSELF and concludes that the whole almost-representation is near a genuine finite-dimensional one, i.e. the two stability notions coincide on hyperlinear approximations.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that is the Becker--Lubotzky no-go for STRICT (same-dimension) HS-stability of infinite hyperlinear Kazhdan groups; this is a positive equivalence between two FLEXIBLE-type notions (weak ucp, flexible) for Kazhdan groups and says nothing about strict stability.
  sln-z-flexibly-hs-stable: that is the open hypothesis for the lattice; this is the general lemma showing that, for any Kazhdan group, Dogon's formally weaker weak ucp-stability is not weaker at all on hyperlinear approximations, so that hypothesis cannot be relaxed by passing to infinite-dimensional dilations.
---

**THEOREM.**  Let `Gamma` be a finitely generated group with Kazhdan's
property (T).  The following are equivalent:

```text
(a) Gamma is weakly ucp-stable (Dogon arXiv:2211.10492 Def 1.5): every
    hyperlinear approximation phi_n : Gamma -> U(d_n) satisfies
    || phi_n(g) - P_n pi_n(g) P_n ||_(2,d_n) -> 0 for genuine unitary
    representations pi_n on Hilbert spaces H^_n supseteq C^(d_n), finite
    or infinite dimensional;
(b) Gamma is flexibly HS-stable on hyperlinear approximations (Dogon Def
    1.2 / Dogon--Vigdorovich Def 1.2 with the quantifier restricted to
    hyperlinear approximations): every hyperlinear approximation phi_n
    satisfies || phi_n(g) - P_n pi_n(g) P_n ||_(2,d_n) -> 0 for genuine
    FINITE-dimensional representations pi_n on C^(D_n) supseteq C^(d_n),
    D_n / d_n -> 1.                                                   (WF1)
```

`(b) => (a)` is a restriction of quantifiers.  `(a) => (b)` is the content:
property (T), applied to the conjugation representation of `Gamma` on the
Hilbert--Schmidt operators of the dilation space, turns the almost-invariant
corner `P_n` into an exactly invariant finite-rank projection of almost the
same rank, whose range carries a genuine finite-dimensional representation
approximating `phi_n`.  The mechanism is Kirchberg's (Math. Ann. 299
(1994), property (T) plus factorization property implies residual
finiteness), run pointwise on a prescribed approximation instead of on the
canonical trace; Dogon's Prop. 1.11 (hyperlinear + (T) + weakly ucp-stable
implies residually finite) is the corollary obtained by composing `(a) =>
(b)` with Becker--Lubotzky's "flexibly stable hyperlinear groups are
residually finite".

**Consequences recorded in the graph.**

- `sl3-z-weakly-ucp-stable` is the `n = 3`, hyperlinear-approximation form
  of `sln-z-flexibly-hs-stable`, not a weaker hypothesis; passing to
  infinite-dimensional dilations buys nothing for Kazhdan groups.  (For
  non-Kazhdan groups it does: Dogon's separating examples are amenable
  non-residually-finite groups, weakly ucp-stable via LLP.)
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

**Literature cousin.**  Fournier-Facio--Willett arXiv:2603.18456v2,
Theorem 1.1: if `C^*(Gamma)` has the LLP and is RFD then every asymptotic
representation (operator, Hilbert--Schmidt or Schatten norm) is near
corners of genuine FINITE-dimensional representations ("very flexibly
stable"); there RFD supplies the finite-dimensional reduction.  Here
property (T) supplies it instead, which is the relevant replacement for
Kazhdan groups, where RFD typically fails (Bekka for `SL_n(Z)`, `n >= 3`;
their Question 1.10 asks whether any infinite Kazhdan group is RFD).

**Boundary.**  The lemma needs full property (T) of `Gamma` (the dilation
space is infinite dimensional, so (T;FD) does not reach it) and says
nothing about asymptotic homomorphisms that are not separating (limit
character not `delta_e`-like), where Dogon's Def 1.2 quantifies more
widely than Def 1.5.
