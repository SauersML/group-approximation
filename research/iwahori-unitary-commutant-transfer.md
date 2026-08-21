---
rg: 2
id: iwahori-unitary-commutant-transfer
kind: claim
title: Almost Iwahori compatibility transfers unitary centralizers between the two SL2(Z) vertices
distinct_from:
  iwahori-local-global-defect-question: that asks to perturb both vertex representations to a compatible pair; this asks only that a unitary almost centralizing the first vertex almost centralize the second.
  iwahori-outlier-repair: that seeks an invertible exact edge intertwiner after small padding; this never constructs an intertwiner and tests only bounded operator-norm unitaries in one vertex commutant.
  sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair: that gives exact commutant equality after the two vertices glue to a finite-dimensional representation of SL2(Z[1/p]); this asks for a uniform approximate version before exact gluing.
---

OPEN.  Let `C=SL_2(Z)`, let `B_+,B_-` be the opposite index-three Iwahori
subgroups in `iwahori-local-global-defect-question`, and let
`sigma:B_+->B_-` be the edge isomorphism.  Fix finite generating sets
`S_C,S_B`.  Prove that there is a modulus `f(x)->0` with the following
dimension-free property.

For every pair of exact representations `pi_+,pi_-:C->U(d)` and every
unitary `v in U(d)`, put

```text
delta_B=max_(b in S_B)||pi_+(b)-pi_-(sigma(b))||_2,
delta_v=max_(c in S_C)||[v,pi_+(c)]||_2.              (IUCT1)
```

Then

```text
max_(c in S_C)||[v,pi_-(c)]||_2
   <=f(delta_B+delta_v).                              (IUCT2)
```

At zero defect this is forced by finite-dimensional co-density: the pair
extends to a representation of `SL_2(Z[1/2])`, whose first vertex has the
same commutant as the whole amalgam.  The open content is uniformity over
dimension and over all exact vertex representations.

By `iwahori-transfer-equals-matricial-commutant-codensity`, the
claim is equivalent to one exact statement in every tracial matrix
ultraproduct: the relative commutant of the first vertex equals the commutant
of the whole Iwahori amalgam.  This is the smallest invariant formulation of
the missing estimate.

This is strictly weaker than global Iwahori repair.  A compatible pair close
to `(pi_+,pi_-)` immediately implies `(IUCT2)`, but `(IUCT2)` asks neither
for a nearby compatible representation nor for an invertible edge
intertwiner.  It only controls unitary points in the first commutant.  Thus
the known warning that an `o(d^2)` low-energy operator space can contain an
invertible matrix does not by itself refute this claim: scalar unitaries are
harmless for `(IUCT2)`, and a counterexample must contain a unitary whose
commutator with the second vertex stays macroscopic.

## Attempts

- **Full Iwahori repair.**  This proves `(IUCT2)` but retains the unresolved
  physical-rank integralization step.
- **Spectral localization alone.**  Insufficient for repairing an arbitrary
  intertwiner.  For this weaker claim it remains useful only if one also
  proves that every unitary in the localized outlier is asymptotically in
  the common commutant.
- **Exact co-density.**  Proves only the zero set.  Compactness at fixed
  dimension is not uniform in `d`, so it supplies no modulus.
- **Concrete falsifier.**  A negative answer requires exact vertex
  representations, edge defect tending to zero, and unitaries `v_d` with
  first-vertex commutators tending to zero but a second-vertex commutator
  bounded below.  Such a sequence would also give the almost-centralizer
  needed by canonical microstates of the HNN candidate.
- **Two-block normal form.**
  `iwahori-transfer-failure-reduces-to-two-block-projection` shows that every
  counterexample may be taken projection-valued after harmless doubling.
  Hence the remaining question is whether the second vertex can have
  macroscopic off-diagonal mass across a decomposition that asymptotically
  reduces the first vertex and the Iwahori edge.  This is narrower than
  repairing an arbitrary low-energy intertwiner.
- **The blocks cannot dilute.**
  `iwahori-transfer-failure-has-two-positive-density-blocks` shows that a
  second-vertex commutator bounded below by `epsilon_0` forces both blocks to
  have normalized rank at least `epsilon_0^2/2`.  Thus a counterexample is a
  positive-density extension-mixing phenomenon, not a vanishing-rank tail.
