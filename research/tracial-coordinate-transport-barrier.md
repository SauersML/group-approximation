---
rg: 2
id: tracial-coordinate-transport-barrier
kind: claim
title: The traced coordinate class cannot be widened to tracial ultraproducts
distinct_from:
  finite-tracial-cstar-transport: That root asks for the largest class where the machinery works; this claim fixes its outer boundary and localizes the failure at one step.
  trace-blindness-sharpness: That claim rules out invariant-size arguments in II_1 factors; this one rules out the corner step of the compressor architecture in tracial coordinates, and does so by an explicit established countermodel.
artifacts:
  - notes/NON_MF_TO_HYPERLINEAR_DIFFERENTIAL_AUDIT.md
---

The coordinate class `C_ftr` of `finite-tracial-cstar-transport` cannot be
widened to normalized-Hilbert--Schmidt (tracial-ultraproduct) coordinates:
no tracial analogue of the central-sign conclusion is true, and the failure
is localized at exactly one step.

1. *Transport is not the obstruction.*  `finite-traced-kazhdan-transport`
   holds with the asymptotic-commutant hypothesis taken in `||.||_2`, so the
   property-`(T)` fixed-space argument survives the passage to tracial
   coordinates unchanged.
2. *The corner is the obstruction.*  The architecture cuts to the negative
   spectral sector of the mark and renormalizes.  By
   `corner-renormalization-cost` this costs `tau(p)^(-1/2)` in the tracial
   world and nothing in the operator-norm world, and `tau(p)` may be `0`.
3. *This is not a technical gap.*  The conclusion itself is false tracially:
   the mark of the literal group lies in the MF residual but not in the
   hyperlinear residual, so no theorem of the form "every tracial matrix
   model kills the mark" can hold.

Hence within this architecture the only tracial freedom left is a corner of
positive trace, i.e. a mark whose spectral sector has positive density --- the
same quantity as the effective-rank profile of
`mf-trace-gap-defect-ratio-models`.
