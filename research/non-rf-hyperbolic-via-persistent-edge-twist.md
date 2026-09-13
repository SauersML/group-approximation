---
rg: 2
id: non-rf-hyperbolic-via-persistent-edge-twist
kind: route
title: A persistent edge-twist moment on a hyperbolic triangle colimit gives a non-residually-finite hyperbolic group
target: non-residually-finite-hyperbolic-group
requires: [hyperbolic-triangle-colimit-with-persistent-edge-twist, edge-twist-extensions-of-triangle-colimits-moment-test]
---

Take `Λ`, `p` and `I_∞ != 0` from the premise, and choose `c` with `<c, I_∞> != 0`. By
(M6) of `edge-twist-extensions-of-triangle-colimits-moment-test`:
- if `Λ` is residually finite, the hyperbolic central extension `Λ_c` has no finite
  quotient injective on its central `C_p`, so it is not residually finite;
- otherwise `Λ` itself is not residually finite.
