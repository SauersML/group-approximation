---
rg: 2
id: kl-via-infinite-dimensional-amplification
kind: route
title: Amplify the regular representation until there is room for a root
target: kervaire-laudenbach-nonsingular-conjecture
requires: []
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Take the left regular representation of the coefficient group, tensor it with
an infinite-dimensional multiplicity space so that it is properly infinite
and absorbs everything in sight, and solve `w(t) = I` for a unitary `T` in
the amplified algebra.  Faithfulness is free — amplification does not lose
it — and the degree argument that produces roots in finite dimensions has, in
this picture, unlimited room to work in.

Dead by `overgroup-room-does-not-supply-a-root`: a faithful `rho` together
with a unitary root *is* a representation of `G_w` faithful on `G`, so
producing the pair is not a step toward the conjecture, it is the
conjecture.  The amplification supplies the room; nothing in it supplies the
root, and the room was never what was missing.

**What survives the demolition.**  Amplification remains the right ambient
whenever the root comes from somewhere else — which is precisely the
hyperlinear proof, where finite-dimensional unitary groups supply a genuine
root by a degree argument and the ultraproduct supplies the room.  The live
version of that division of labour is
`window-controlled-finite-dimensional-root-theorem`.
