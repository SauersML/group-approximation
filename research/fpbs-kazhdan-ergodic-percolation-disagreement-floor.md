---
rg: 2
id: fpbs-kazhdan-ergodic-percolation-disagreement-floor
kind: claim
title: Ergodic invariant site percolation on a Kazhdan group has neighbour disagreement at least kappa squared p(1-p)
invalidates:
  - fpbs-dead-fiid-hutchcroft-pete-limit-recursion
distinct_from:
  fpbs-kazhdan-groups-have-cost-one: that is the imported Hutchcroft--Pete theorem giving one cost-one action for every infinite Kazhdan group; this is a spectral lower bound on neighbour disagreement for every ergodic invariant percolation, which limits how their construction can be made admissible.
artifacts:
  - research/artifacts/fpbs/docs/normal-subgroup-fixed-price.md
---

**Proposition D of the linked note, Section 5.** Let `(S, kappa)` be a
Kazhdan pair for `Gamma`, and let `mu` be an ergodic invariant probability
measure on `{0,1}^Gamma` with marginal `p = mu(omega(e) = 1)`. Then
`max_(s in S) mu(omega(s) != omega(e)) >= kappa^2 p (1-p)`.

*Proof.* Apply the Kazhdan inequality to `f = 1_(omega(e)=1) - p` in `L^2_0(mu)`,
which contains no invariant vectors. Here `||f||^2 = p(1-p)` and
`||pi(s) f - f||^2 = mu(omega(s) != omega(e))`.

**Consequence.** Every factor of i.i.d. is ergodic, so every
factor-of-i.i.d. site percolation with marginal `p` on a Cayley graph of a
Kazhdan group keeps neighbour disagreement at least `kappa^2 p (1-p)`. The
Hutchcroft--Pete recursion reaches its non-ergodic limit
`p delta_V + (1-p) delta_empty` only by driving that disagreement to zero, so
it cannot stay inside the factor-of-i.i.d. class. An admissible version of the
strategy for `fpbs-kazhdan-sparse-spines` must therefore produce its
condensation at a stage where disagreement is still bounded below.
