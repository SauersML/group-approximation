---
rg: 2
id: common-corner-mutual-bicommutant-extraction
kind: claim
title: Two transverse robust packets exactify as mutual commutants on one positive-density corner
artifacts:
  - research/artifacts/nonhyperlinear-breakout-portfolio-2026-08-21.md
distinct_from:
  full-packet-bicommutant-synchronization: that starts with one raw packet and asks every unitary in its coordinate commutant to commute with one transported carrier; this recovers two named word-generated packet algebras and identifies each as the full commutant of the other.
  tensor-independent-child-carrier-gap: that gives an analytic distance floor once two trace-independent child algebras and one common carrier are supplied; this is the finite-dimensional perturbation theorem intended to identify the physical tensor factors before applying such a floor.
  paired-same-reservoir-boundary-lemma: that follows a compressor branch and charges leaving one reservoir; this makes the reservoir itself observable as a second packet algebra.
---

Let one fixed finite label packet and one scalable word-generated transverse
reservoir algebra be represented in a compressor presentation.  Suppose a
matrix microstate has vanishing packet, generation, and cross-commutation
defects and a canonical spectral projection `P` of trace at least `alpha>0`
on which both structures occur.  Then, after a dimension-free `o(1)`
perturbation and an `o(1)` change of `P`, there are exact finite-dimensional
semisimple algebras `Atilde,Btilde` on the same corner satisfying

```text
Atilde' cap P M_d P = Btilde,
Btilde' cap P M_d P = Atilde,
W*(Atilde,Btilde)=P M_d P.                              (CCMB1)
```

In particular `Atilde ~= M_r tensor I_m` and
`Btilde ~= I_r tensor M_m` on each selected simple summand.  A compressor
cycle that enlarges the simple degree of `Atilde` while returning the named
`Btilde` packet to itself must therefore lose positive normalized rank or pay
a packet/transport defect: the anonymous multiplicity reservoir has become a
second word-generated algebra and cannot exchange roles with the label factor.

## Attempts

- **A second fixed finite group cannot expose an unbounded reservoir.** Its
  irreducible degrees are bounded, and repetitions leave a common spectator
  algebra.  Thus finite-group exactification may anchor the label coordinates
  but cannot by itself produce the variable `M_m` factor in `(CCMB1)`.  The
  second algebra must be scalable (for example a word-generated matrix tape),
  or an independent argument must kill the residual spectator.  This is a
  load-bearing compiler requirement, not bookkeeping.
- **Rectangular firewall.** Add the proposed second packet to the exact
  `rectangular-escape`.  If the joint words still admit a larger tensor
  decomposition with an unused spectator factor, `(CCMB1)` is false for that
  packet choice.  The packet pair must exhaust the corner.
- **Bass--Serre firewall.** A finite graph of finite groups has exact finite
  quotient models, so endpoint type matching alone cannot force `(CCMB1)` or
  charge forbidden rank-one mass.  The required fullness must come from
  genuinely transverse compressor/holonomy relations.
- **Hybrid endpoint.** Once `(CCMB1)` pins one transverse generator, the
  fixed-PI-degree claim needs only one tuple outside every embedded
  `M_r` subfactor; conversely the PI value can certify fullness.  The two
  targets should be tested together on the same exact rectangular model.
