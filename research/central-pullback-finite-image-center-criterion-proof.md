---
rg: 2
id: central-pullback-finite-image-center-criterion-proof
kind: route
title: Trap the residual mark in the center of every finite kernel image
target: central-pullback-finite-image-center-criterion
requires: []
artifacts:
  - research/artifacts/rips-central-pullback-finite-image-centers-2026-09-12.md
---

The projection `P -> G` has finite central kernel `A`, and `P -> E` has
kernel `N`, embedded by `n -> (1,n)`. The element `z_P=(z,1)` has order
exactly `p` and is central.

For any surjection `phi:P -> F` with `F` finite, put `J=phi(N)`. Since
`N` is normal in `P`, the quotient map to `F/J` factors through `E`. The
finite-residual hypothesis on `z` gives `phi(z_P) in J`. Centrality gives
`phi(z_P) in Z(J)`. Its order divides `p`, so the center hypothesis forces
`phi(z_P)=1`. This proves finite invisibility for every finite image.

If `G` is word-hyperbolic, a finite-kernel extension of it is finitely
generated and quasi-isometric to it, so `P` is word-hyperbolic. A
torsion-free subgroup of finite index in `P` would have a torsion-free
normal core of finite index. The finite quotient by that core would
detect `z_P`, contradicting what was just proved.

Finally a finite homomorphic image of a quotient of a group `H` is also a
finite homomorphic image of `H`. Thus the center hypothesis passes to
quotients, as asserted.
