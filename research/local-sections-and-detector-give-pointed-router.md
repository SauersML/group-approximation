---
rg: 2
id: local-sections-and-detector-give-pointed-router
kind: route
title: Glue source-local router sections on the primitive zero face
target: source-specific-pointed-rank-router-face
requires:
  - pointed-router-local-section-system
  - rank-router-gluing-cokernel-has-primitive-detector
---

## Why sufficient

`pointed-router-local-section-system` supplies the required affine hybrid
blocks `(SPR1)` locally on every chart of the one distinguished source packet,
with a dimension-independent microstate modulus.  It deliberately leaves only
the relative source gauges on chart overlaps undetermined.

`rank-router-gluing-cokernel-has-primitive-detector` quotients exactly those
local gauge changes.  On the finite pointed face

```text
gamma_glue = 0                                             (LGD1)
```

its completeness clause makes the residual overlap class a coboundary, so a
choice of local source gauges makes all branchwise `R_f,S_f` sections agree on
one common packet.  Because the detector is a fixed integer combination of
the available rank/mixed-moment coordinates, `(LGD1)` is a finite pointed
moment condition visible to canonical matrix microstates.

The distinguished perfect source lies on `(LGD1)`, giving one-source exact
completeness.  The tensor-closure witness has nonzero `gamma_glue`, so it is
excluded without asserting any universal extension theorem for arbitrary
zero-overlap pairs.  The glued local estimates therefore give the global
`(SPR1)` conclusion and the required non-tensor-closed source face, which is
exactly `source-specific-pointed-rank-router-face`.
