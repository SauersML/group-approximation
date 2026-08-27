# Kun--Thom full-actor divergent-leakage audit

Date: 2026-08-26

## Question

After `kt-infinite-index-returns-force-divergent-edge-leakage` and its sharp
small-rotation calibration, can the presence of the actual strict compressor
inside the full residually finite Kazhdan actor itself rule out divergent
unnormalized edge leakage?

## Answer

No.  The new node
`vanishing-weight-block-carries-full-actor-edge-leakage` gives a direct-sum
countermodel.  A dominant amplified exact finite-quotient representation
supplies the full actor relations and the canonical character.  A physical
summand of weight `delta_r->0` carries the diagonal small-rotation model with
leakage asymptotic to `2sqrt(2^r)`.  Arbitrary relation errors on that summand
cost at most `2sqrt(delta_r)` globally, while the unnormalized superoperator
leakage is unaffected by its physical trace weight.

The countermodel deliberately has exterior-return expectation tending to
one, not zero, because the dominant exact finite-image return is algebraically
absorbed by the edge algebra.  Therefore it does not solve or refute reduced
MF.  It sharpens the remaining target to a co-location statement: return
expectation disappearance and divergent leakage must be forced on the same
nonvanishing trace sector.  Merely adjoining the full actor relations to the
divergence law cannot close Certificate C.

## Duplication check

- `canonical-moments-admit-divergent-edge-leakage` has the leakage geometry
  but only an amenable direct-product table and no strict compressor.
- `kt-full-actor-extension-is-locally-hs-unstable` has the full actor but uses
  a central lamp extension and does not calculate divergent edge leakage.
- `coprime-sector-robustness-proof` records the general tracial invisibility
  of vanishing summands in another arithmetic lane; it does not identify the
  failure of the unnormalized Kun--Thom leakage invariant.

No local heavy computation was used.
