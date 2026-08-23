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

Every zero-, one-, or two-point subset is a cap.  Of the thirty-five triples,
exactly the seven Fano lines fail to be caps, leaving twenty-eight cap
triples.  The preceding classification gives exactly seven cap quadruples
and none of greater size.  This proves `(FMC4)` and the total
`1+7+21+28+7=64`.

A subset is a line-blocking set exactly when its complement contains no
line, hence exactly when that complement is a cap.  The maximum cap size four
gives minimum blocking size three.  A three-point blocker has a four-point
cap complement, so the complement is `C_lambda`; its complement is the
kernel of `lambda` with zero removed, which is a Fano line.  Conversely every
line has a maximal-cap complement.
