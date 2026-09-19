---
rg: 2
id: fpbs-stationary-set-recurrence-separates
kind: claim
title: A unique infinite cluster meets every independent walk range and every independent aperiodic subrelation class infinitely often, so almost surely finite visits above p_c separate the thresholds
distinct_from:
  fpbs-green-visit-criterion-implies-nonuniqueness: that needs finite expected visits of simple random walk and uses the Harris--FKG bound tau >= theta^2; this needs only almost surely finite visits, allows any step law and any aperiodic subrelation class, and holds for every invariant percolation with a unique infinite cluster, by Poincaré recurrence.
  fpbs-relative-gap-along-any-subgroup-separates: that is the inequality p_c(I;G) <= p_u for deterministic subgroups via Hutchcroft--Pan; this is the same separation for random sets independent of the percolation, of which subgroups are the orbit-relation special case.
  fpbs-soft-collapse-kills-relative-gap-proofs: that uses invariant finite sets inside a subgroup to kill soft relative-gap proofs; this proves the positive recurrence statement for walk ranges and arbitrary aperiodic relations, and is the input of the extension fpbs-soft-collapse-kills-stationary-set-gap-proofs.
artifacts:
  - research/artifacts/fpbs/docs/stationary-set-recurrence-2026-09-19.md
---

**ESTABLISHED.** Theorem 1, Lemma 2 and Corollary 3 of
`research/artifacts/fpbs/docs/stationary-set-recurrence-2026-09-19.md`.

Let `G = Cay(Gamma,S)` and let `P` be any `Gamma`-invariant bond percolation
law. An **independent stationary set** is one of the following, independent of
`omega`:

* **(W)** the path `X_n = xi_1 ... xi_n` of an i.i.d. walk with an arbitrary
  step law `mu`, with `V = #{n : X_n in C_e}`;
* **(R)** `A(y) = {g : (g^{-1}y, y) in R'}`, where `R'` is a Borel subrelation
  with a.e. infinite classes of the orbit relation of a free pmp action
  `Gamma ↷ (Y,nu)`, with `V = |C_e ∩ A(y)|`.

Infinite subgroups are the case (R) with `R'` the orbit relation of the
subgroup on the Bernoulli shift.

**Theorem.** Almost surely on {`omega` has exactly one infinite cluster and
`e` lies in it}, `V = infinity`.

**Corollary.** For Bernoulli percolation, if `V < infinity` a.s. at some
`p > p_c(G)`, then `p_c(G) < p <= p_u(G)`.

The proof is Poincaré recurrence for the skew product
`(omega, xi) -> (xi_1^{-1} omega, shift xi)` in case (W). In case (R) it is the
fact that a Borel set meets a.e. class of an aperiodic pmp relation in
0 or infinitely many points, applied to the lift of `R'` to `Omega x Y`. No
Bernoulli property is used, only invariance, independence and uniqueness.
