---
rg: 2
id: whitehead-diagonal-not-multiplicative-proof
kind: route
title: Compare the lower blocks of w(XY) and w(X)w(Y)
target: whitehead-diagonal-map-is-not-multiplicative
requires: []
---

Block multiplication gives `w(X) w(Y) = diag(XY, X^-1 Y^-1)`, while
`w(XY) = diag(XY, (XY)^-1) = diag(XY, Y^-1 X^-1)`.

The two agree exactly when `X^-1 Y^-1 = Y^-1 X^-1`. Inverting both sides turns
this into `YX = XY`.

For a nonabelian `H`, pick non-commuting `X, Y in H`. Then `w(XY) != w(X) w(Y)`,
so `w` is not a homomorphism on `H`. Appending identity blocks does not change
the lower-block comparison. QED
