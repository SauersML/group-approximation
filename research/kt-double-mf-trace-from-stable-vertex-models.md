---
rg: 2
id: kt-double-mf-trace-from-stable-vertex-models
kind: route
title: Stable-vertex MF-trace models make the canonical double trace an MF trace
target: reduced-amalgam-canonical-trace-is-mf
requires: [kt-double-stable-vertex-mf-trace-models, stable-vertex-mf-trace-models-need-inequivalent-marginals, vertex-mismatch-needs-nonextendable-clifford-orbits]
---

The models of the first prerequisite are operator-norm asymptotic
homomorphisms of `D` whose normalized traces converge to the canonical trace.
Extending linearly to the group ring and continuously to `C*(D)` gives the
maps of `(RAT1)`.

The second prerequisite adds nothing to sufficiency.  It fixes the shape any
witness must have: inequivalent Kazhdan marginals at every large stage, and no
permutation vertex models.  Unlike the reduced-MF route, this route has no
Kazhdan vertex gate (`infinite-kazhdan-group-with-mf-reduced-cstar`), because
residually finite vertex groups already carry MF regular traces through finite
quotients.
