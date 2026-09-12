---
rg: 2
id: kun-thom-lamp-quotients-sofic-radical-proof
kind: route
title: Sofic images of the quotient are sofic images of the wreath, and the fibre-parity quotient is residually finite
target: kun-thom-lamp-quotients-have-lamp-sofic-radical
requires:
  - kun-thom-wreath-sofic-radical-is-fibre-parity-kernel
artifacts:
  - research/artifacts/kun-thom-lamp-quotient-hosts-2026-09-12.md
---

Let `q : W -> H_U` be the quotient map. A homomorphism `psi` from `H_U` into a sofic group gives
`psi o q`, which kills `Rad_sof(W) = K_even`. So `psi` kills `K_even/U`. Conversely
`H_U/(K_even/U) = W/K_even = W_N` is residually finite by part 2 of the radical theorem, hence
sofic. So `K_even/U` is the kernel of a homomorphism into a sofic group. Theorem A of the
artifact.
