---
rg: 2
id: stw50-kirchberg-kernel-loops-proof
kind: route
title: Normalize the six graph-model loops to obtain four rotation-kernel generators
target: stw50-explicit-basis-of-rotation-retraction-kernel
requires:
  - stw50-six-kirchberg-circle-loops
  - stw50-rotation-loops-form-a-direct-summand
artifacts:
  - research/artifacts/stw50-six-kirchberg-loops-2026-09-05.md
  - research/artifacts/stw50-rotation-loop-retraction-2026-09-04.md
---

Use the preferred marking of the six-loop invariant matrix. Take
sigma_2, sigma_4, rho_1 sigma_1^{-1}, rho_2 sigma_3^{-1}, with
pointwise composition and inversion. Their columns are the four
signed standard basis vectors whose first and third coordinates
vanish. They give an integral basis of that coordinate kernel.

Fix a unital classification identification with A_theta tensor
O_infinity sending e,beta to [1],q and x,y to [U tensor 1],
[V tensor 1], where epsilon(q)=0 in the established rotation
retraction. Naturality identifies the coordinate kernel with the
kernel of that retraction. Transporting these four actual loops
therefore proves the **Kirchberg alternative** of the target.
The stably finite alternative is not asserted by this route.
