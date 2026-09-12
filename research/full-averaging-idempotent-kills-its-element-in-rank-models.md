---
rg: 2
id: full-averaging-idempotent-kills-its-element-in-rank-models
kind: claim
title: A full averaging idempotent kills its element in every rank model
distinct_from:
  anti-central-rank-models-kill-ternary-corner-witnesses: that concerns the anti-central summand of the ternary Leavitt unit group algebra and needs the central involution together with the pair w, d; this is the general statement for any group and any finite-order element of order prime to the characteristic, with no central element.
  full-idempotent-ring-has-properly-infinite-unit: that says a ring with a full idempotent different from 1 has a properly infinite unit; this says what fullness of an averaging idempotent forces in rank models of the group.
artifacts:
  - research/artifacts/thompson-v-rank-support-and-kernel-transfer-2026-09-12.md
---

Let `F` be a field of characteristic `p`, `H` a group, `g` in `H` of finite order `m` with `p`
not dividing `m`, and `e_g = m^-1 (1 + g + ... + g^(m-1))` in `F[H]`. If `c e_g b = 1` for some
`b, c` in `F[H]`, then `sigma(g) = 1` for every group homomorphism `sigma : H -> M^x` into an
`F`-algebra `M` carrying a Sylvester rank function faithful on idempotents. Examples of `M` are
`M_n(k)` and a rank ultraproduct over a field `k` of characteristic `p`. The same holds for the
matrix form `C (e_g I_n) B = I_n`.

Proof: Section 1 of the artifact, route `full-averaging-idempotent-rank-model-proof`.
