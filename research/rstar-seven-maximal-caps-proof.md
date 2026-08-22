---
rg: 2
id: rstar-seven-maximal-caps-proof
kind: route
title: Extend every Fano cap to a nonzero affine character fiber
target: rstar-fano-caps-have-seven-maximal-parity-covers
requires:
  - rstar-fano-ghost-affine-hull-criterion
---

If `u,v in C_lambda`, then `lambda(u+v)=0`, so `C_lambda` contains no Fano
line and is a cap.  Conversely a cap has at most four points.  For at most
three points, the points are linearly independent (otherwise three contain
`u,v,u+v`), so prescribe value one on them and extend to a linear
functional.  For a four-point cap, any three points are independent and the
fourth is their sum; the same functional takes value `1+1+1=1` on the
fourth.  It is nonzero and contains the cap in its one-fiber.

Every `C_lambda` has four points, the maximum cap size, so the seven nonzero
functionals give exactly the seven maximal caps.  Translating back from the
ghost gives `(FMC3)` and the stated two-row affine branch.
