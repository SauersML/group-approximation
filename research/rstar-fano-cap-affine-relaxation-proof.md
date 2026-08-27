---
rg: 2
id: rstar-fano-cap-affine-relaxation-proof
kind: route
title: Apply tracial support linearization and observe that every affine context remains honest
target: rstar-fano-cap-support-preserves-nonru-affine-relaxation
requires:
  - tracial-support-affine-linearization
  - rstar-fano-ghost-affine-hull-criterion
---

The first requirement supplies an exact tracial representation of the LCS
whose local solution spaces are `Aff(S_c)`.  The second says each of these
spaces is contained in the original `R_*` relation.  Restriction along the
unchanged shared-variable rows therefore sends every LCS trace to a BCS
trace.  Connes embeddability is preserved under this restriction, so a CE
trace of the LCS would contradict the assumed non-RU property of the BCS.
