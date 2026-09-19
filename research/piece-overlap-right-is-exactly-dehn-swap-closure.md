---
rg: 2
id: piece-overlap-right-is-exactly-dehn-swap-closure
kind: claim
title: The residual overlap configuration is equivalent to full Dehn swap closure, so the critical-pair analysis bought configuration and not strength
distinct_from:
  cascade-landing-from-deep-arc-and-beta: that is the descent lane; this is the rewriting lane, and the two remain separate routes -- this equivalence collapses a step INSIDE the rewriting lane and says nothing about the descent one.
  deep-two-factor-regime-is-empty: that is a genuine narrowing, an emptiness theorem that removes configurations from an open leaf; this is the opposite outcome for a different reduction, and the pair is worth reading together.
artifacts:
  - GroupApproximation/Sofic/GreendlingerDehnCritical.lean
  - GroupApproximation/Sofic/GreendlingerDehnSwap.lean
  - GroupApproximation/Sofic/GreendlingerPieceOverlapProof.lean
---

For a `C'(1/6)` family of cyclically reduced relators,

```text
PieceOverlapRight R  <-->  DehnSwapClosed R.
```

This is `pieceOverlapRight_iff_dehnSwapClosed`, the two halves being
`dehnSwapClosed_of_pieceOverlap` (the critical-pair analysis) and
`pieceOverlapRight_of_dehnSwapClosed` (a free upgrade).

`DehnSwapClosed` is the blunt statement that Dehn reducibility survives every
swap.  `PieceOverlapRight` is the narrow one: a single overlap of two distinct
relators, in one regime.  The critical-pair analysis was expected to be a
*reduction*; the iff says it is not.

## What is refuted

The belief that the critical-pair work had weakened the obligation.  It reduced
the **configuration** the statement quantifies over --- one overlap in one
regime instead of every pair of moves --- and left the logical strength
untouched.  A proof of the narrow residual must supply a first move for a word
which, by `no_dehn_step_at_far_arm` and `no_dehn_step_at_replacement`, has none
at either occurrence the configuration names; the move can only come from how
the derivation of the step's output meets the surrounding context.  That is the
same difficulty as before, relocated.

The mirror configuration is likewise not independent:
`pieceOverlapLeft_of_right` derives `PieceOverlapLeft`, and
`pieceOverlapRight_iff_firstStep` collapses `PieceOverlapFirstStep` into the
same statement.  Three names, one obligation.

## What is NOT refuted, and a correction worth recording

This does **not** collapse the two routes to the Greendlinger conclusion.  The
descent lane (`CascadeLanding`) and the rewriting lane (`PieceOverlapRight`)
are still separate, and no theorem in the tree relates them; the "second route"
language in the router and relative-small-cancellation headers refers to that
pair, and it survives.  Reading this equivalence as killing the second route is
a category error --- it kills a *reduction inside* the second route.

The circle also closes on one side only: `dehnFreeClosed_of_pieceOverlap` sends
the residual to free closure, and nothing sends free closure back.
