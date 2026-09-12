---
rg: 2
id: z-stable-unital-algebras-are-k1-bijective
kind: claim
title: Unital Jiang--Su stable C*-algebras are K1-bijective
distinct_from:
  stw99-lxxvi-z-stabilization-kills-unstable-unitary-kernel: that applies Jiang's matrix-stabilization theorem to a scalar extension to kill a higher unstable kernel; this records the size-one component statement U(A)/U_0(A) = K_1(A) for every unital Z-stable algebra.
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

If `A` is a unital C*-algebra with `A ~= A tensor Z`, the canonical map

```text
U(A)/U_0(A) -> K_1(A)
```

is a group isomorphism. In particular every unital Z-stable algebra is
K1-injective, so a unital algebra that is not K1-injective is not Z-stable.

This is the `i = 0` case of Jiang's theorem that
`pi_i(U(A)) -> K_(i-1)(A)` is an isomorphism for every unital Z-stable `A`.
