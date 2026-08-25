---
rg: 2
id: property-t-free-manuscript-from-leavitt-collapse
kind: route
title: Rebuild the manuscript from the intrinsic Leavitt collapse and algebraic radical calculus
target: property-t-free-manuscript-results
requires:
  - property-t-free-leavitt-full-mf-radical
  - property-t-free-st20-collapse-transfers-to-el12
  - mf-radical-functoriality
  - countable-mf-groups-are-epireflective
  - compression-defect-dies-in-finite-dimensions
  - binary-leavitt-elementary-group-is-simple
  - full-leavitt-idempotent-defect-saturation
  - corona-projective-hilbert-hotel-cancellation
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/PropertyTFreeMFCollapse.lean
---

Once `property-t-free-leavitt-full-mf-radical` supplies the intrinsic
rank-twenty Steinberg seed,
`property-t-free-st20-collapse-transfers-to-el12` carries it through the
canonical elementary quotient and the explicit Leavitt rank equivalence to
the manuscript's literal group `EL_12(R)`.  The remainder is algebraic
assembly.

* Full radical gives non-MF because the binary-Leavitt group is nontrivial.
* Root normal generation and simplicity turn the killed marked root into
  total MF invisibility.
* MF-radical functoriality and the epireflection theorem give the quotient,
  pullback, closure, and universal-factorization statements.
* The prescribed-visible-quotient construction uses only amalgam/HNN normal
  forms plus the full-radical seed; it does not need a rigidity property of
  the seed.
* Finite-dimensional commutant rigidity remains the elementary fact that an
  injective endomorphism of a finite-dimensional commutant is surjective.

The Lean endpoint must re-export these conclusions directly from a proof cone
rooted at the intrinsic collapse.  It must not import the current
`NormalKazhdan`, `KazhdanTransport`, Property-T bridge, or Hilbert-hotel
Kazhdan endpoint modules merely to recover closed declarations with the same
conclusions.
