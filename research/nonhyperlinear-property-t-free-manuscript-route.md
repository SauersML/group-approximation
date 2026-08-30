---
rg: 2
id: nonhyperlinear-property-t-free-manuscript-route
kind: route
title: Rebuild the manuscript with the authenticated BCS corner as its first endpoint
target: property-t-free-manuscript-results
requires:
  - nonhyperlinear-property-t-free-explicit-mf-witness
  - property-t-free-leavitt-full-mf-radical
  - property-t-free-torsion-free-full-mf-radical
  - property-t-free-st20-collapse-transfers-to-el12
  - mf-radical-functoriality
  - countable-mf-groups-are-epireflective
  - compression-defect-dies-in-finite-dimensions
  - binary-leavitt-elementary-group-is-simple
  - full-leavitt-idempotent-defect-saturation
  - corona-projective-hilbert-hotel-cancellation
artifacts:
  - research/artifacts/nonhyperlinear-normal-augmentation-source-audit-2026-08-30.md
---

Use `nonhyperlinear-property-t-free-explicit-mf-witness` for the manuscript's
first explicit countable group and named corona-invisible element.  Use the
independent binary-Leavitt collapse and rank-transfer inputs for the full
MF-radical version, and the independent torsion-free input for the final
finitely presented acylindrically hyperbolic theorem.  The remaining listed
inputs are the established algebraic radical and simplicity calculus already
used by `property-t-free-manuscript-from-leavitt-collapse`.

This route makes the logical boundary explicit: the authenticated BCS corner
can replace Property `(T)` for endpoint 1, but it does not by itself imply
the binary-Leavitt or torsion-free endpoint.  Therefore the single live gate
on the BCS branch is `nonhyperlinear-bloop-central-sign-corner`, while the two
unrelated obligations remain visible rather than being hidden as assumptions.
