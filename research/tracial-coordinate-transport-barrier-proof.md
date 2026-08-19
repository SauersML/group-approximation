---
rg: 2
id: tracial-coordinate-transport-barrier-proof
kind: route
title: Established countermodel plus the localization of the corner step
target: tracial-coordinate-transport-barrier
requires: [mf-hyperlinear-radical-divergence, finite-traced-kazhdan-transport, corner-renormalization-cost]
artifacts:
  - notes/NON_MF_TO_HYPERLINEAR_DIFFERENTIAL_AUDIT.md
---

## Why sufficient

Item 1 is the statement of `finite-traced-kazhdan-transport`, whose
hypothesis is allowed in `||.||_(2,tau_k)`; its proof passes through the
tracial ultraproduct in any case, so nothing in it distinguishes the two
norms.

Item 2 is `(C1)`--`(C2)` of `corner-renormalization-cost`, together with the
observation that the corner produced by the architecture is the negative
spectral sector of the mark, whose trace is exactly the relative rank of that
sector and is not bounded below by anything in the hypotheses.

Item 3 is `mf-hyperlinear-radical-divergence`: the literal mark lies in the
operator-norm MF residual and outside the hyperlinear residual, the latter
because an explicit Connes-embeddable Clifford model sends it to `-1`.  A
tracial analogue of the central-sign obstruction would place it in the
hyperlinear residual, contradicting that detector.  The same conclusion
follows independently from `hyperlinear-not-imply-mf`: its witness is sofic,
hence hyperlinear, hence has faithful tracial models of every element, while
being non-MF.

Therefore the class of coordinates for which the full architecture is valid
is bounded above by the requirement that nonzero corners carry states, which
is item 2 of `faithfully-traced-unital-coordinates` and fails precisely for
tracial ultraproducts.  End proof.
