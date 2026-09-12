---
rg: 2
id: kt-relative-functor-raw-map-defect-estimate-proof
kind: route
title: Localized bridge counting, word labels and roundtrip transport
target: kt-relative-functor-raw-map-defect-estimate
requires: []
artifacts:
  - GroupApproximation/KunThom/RelativeFunctorEstimate.lean
---

## Direct proof, machine-checked

- **Bridges.** Take the bridge realized by `q` and a source point. The bridge fails
  to intertwine there only if one of four things happens:
  - the point is missing from the source;
  - a block action is incompatible at the point;
  - `q` fails to conjugate at the point;
  - the image is an incompatible point of the target.
  The reverse of the bridge realized by `q` is the bridge realized by `q⁻¹`
  (`symm_bridge_inv`), so the same count controls it.
- **Transport.** `FinitePartialBijection.card_equivarianceDefect_sandwich_le` splits
  the transported defect into three parts: the reversed source bridge, the arrow,
  and the target bridge.
- **Words.** `card_equivarianceDefect_wordAct_le` charges the arrow
  `|S| · (sourceDefect + k · defect)` for the word labels.
  `compatFailure_wordBlockAction` identifies the compatibility failures of the word
  labels with `wordCompatFailure`.
- **Transport back.** The argument combines three steps with the triangle
  inequality:
  - `twoSidedDisagreement_sandwich_roundtrip_le` for the round trip through the
    bridges realized by `u⁻¹` and then `u`;
  - `twoSidedDisagreement_sandwich_le` for the Lipschitz step;
  - `symm_bridge_inv`, which identifies the reversed bridges with the reference
    bridges.

Probe GREEN at base c14170721, tag 0912-131642-74704. All eleven printed axiom
closures are `[propext, Classical.choice, Quot.sound]`.
