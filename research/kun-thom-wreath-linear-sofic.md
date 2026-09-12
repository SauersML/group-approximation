---
rg: 2
id: kun-thom-wreath-linear-sofic
kind: claim
title: The Kun--Thom nonsofic wreath is linear sofic over C
distinct_from:
  hyperlinear-wreath-model: that asks for normalized Hilbert--Schmidt microstates of the same wreath; this asks for normalized-rank matrix models, and neither conclusion is known to imply the other.
  kun-thom-wreath-stably-finite: that proves stable finiteness of the group algebras, a necessary condition for linear soficity over each field; this is linear soficity itself.
---

OPEN.  Let `W = (directSum_(G/Gamma) Z/2) semidirect G` be the Kun--Thom wreath
over the Theorem E pair of [[kun-thom-nonsofic-wreath]].  Show that `W`
embeds in a rank-metric ultraproduct `prod_omega GL_(n_k)(C)/d_omega`.

Payoff: `W` is nonsofic, so this establishes [[linear-sofic-nonsofic-group]]
and answers Arzhantseva--Paunescu Question 8.5 negatively.

## Attempts

- **Glebsky-style permanence.** `W` is weakly sofic through Glebsky's theorem
  that a residually finite quotient over a weakly sofic kernel keeps the
  group weakly sofic.  His proof characterizes weak soficity by systems of
  equations solvable in all finite groups.  That characterization forgets the
  metric, so it cannot certify the rank metric.  No rank analogue is known.
- **Finite quotients of the actor.** Models factoring through finite
  quotients `G -> G_N` make the compression an equality in `G_N`, so they
  kill the lamp commutator `e_(t Gamma) e_(gamma t Gamma)` for `gamma` outside
  `t Gamma t^-1`.  A positive model needs invertible matrices for the
  compressor that do not come from a finite permutation action.
- **Hayes--Sale permanence.** Their standard-wreath permanence for linear
  soficity needs a sofic action.  `W` is a permutational wreath over the
  nonsofic coset action (Kun--Thom Corollary D).  It does embed in the
  unrestricted standard wreath `(Z/2)^G semidirect G` through right
  `Gamma`-invariant functions, but no permanence theorem covers unrestricted
  wreaths over nonamenable actors.
