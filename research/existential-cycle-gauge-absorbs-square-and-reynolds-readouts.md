---
rg: 2
id: existential-cycle-gauge-absorbs-square-and-reynolds-readouts
kind: claim
title: An existential chord gauge absorbs central-square and marginal Reynolds readouts
distinct_from:
  central-square-orients-transverse-ledger: that proves W squared equals J orients a raw holonomy lift already named by the base; this proves the clause has no soundness when W is the freely chosen product of auxiliary packet transporters.
  termwise-finite-reynolds-holonomy-has-zero-rank-gap: that rules out unequal Reynolds ranks under a group conjugacy; this shows the returned marginal Reynolds projection is pointwise fixed by the residual commutant gauge even before comparing ranks.
  oracular-local-block-detectors-miss-balanced-cycle-holonomy: that identifies the free cycle datum; this tests the proposed odd-phase and adjoint-average readouts and proves they do not consume it.
---

Consider a connected finite atlas of exact packet representations.  Suppose
every edge transporter is an auxiliary existential unitary intertwining the
specified shared marginal packet.  Fix transporters along a spanning tree.
For a chord `e`, let `W_e` be the resulting return around its fundamental
cycle and let `N_e` be the represented shared marginal algebra at the base
vertex.  Then

```text
W_e in N_e',                                             (EHG1)
```

and the chord transporter can be changed, without altering any edge
covariance relation, so that `W_e` becomes **any prescribed unitary** in
`N_e'`.

## Proof

Choose one chord intertwiner `T_e^0`.  The product around the cycle is an
intertwiner from the base marginal representation to itself, so its return
`W_e^0` lies in `N_e'`.  Every other chord intertwiner has the form
`T_e^0 Z` (with the harmless source/target convention reversed if needed)
for `Z` in the corresponding marginal commutant.  After transporting `Z`
back along the fixed tree, the cycle return is `W_e^0 Z`.  Given
`R in U(N_e')`, choose `Z=(W_e^0)^*R`.  This changes no local packet,
isotypic multiplicity, marginal rank, or edge intertwining equation, and
makes the return exactly `R`.  Distinct fundamental chords may be treated
independently.

## Two proposed readouts

1. **Odd central square.**  On a fixed `J=-1` sector, take `R=iI`; on the
   `J=+1` sector take `R=I`.  Then `R^2=J`.  Thus adjoining the ordinary
   clause `W_e^2=J` merely chooses an auxiliary chord gauge.  It does not
   charge losing mass.  The positive theorem
   `central-square-orients-transverse-ledger` remains applicable only after
   a raw lift has been fixed independently of these existential
   transporters.
2. **Marginal Reynolds average.**  Let `mathcal R_(N_e)` be the adjoint
   Reynolds projection of the finite marginal packet.  Since every allowed
   return lies in `N_e'`,

   ```text
   Ad(W_e) mathcal R_(N_e)=mathcal R_(N_e) Ad(W_e)
   ```

   and changing the chord gauge does not alter its rank or its returned
   marginal fixed algebra.  Termwise finite-table transport therefore
   supplies no curvature.  A Reynolds test can become sensitive only by
   comparing a larger context algebra not fixed by the marginal gauge; that
   is already a nontransport relative-position observable, not the raw
   marginal Reynolds return.

Finite-sheet signed-permutation models realize the same freedom in finite
dimensions, so amplification does not remove the countermodel.

## Surviving readout

A one-sided charged compression is qualitatively different.  Rephasing a
unitary intertwiner cannot make a nonzero source projection embed into a
strictly smaller target in finite dimension.  Such a rank-asymmetric
section could therefore consume the cycle gauge while a properly infinite
exact completion absorbs it.  Constructing it as an ordinary word on the
same selected packet is precisely the existing
`type-filtered-proper-corner-return-actuator`; the square and marginal
Reynolds proposals do not bypass that gate.
