---
rg: 2
id: fpbs-uniform-l2-gap-from-relator-cylinders
kind: route
title: Cover the compact space by the high-girth patch and finitely many relator cylinders
target: fpbs-uniform-l2-gap-marked-groups
requires: [fpbs-uniform-l2-gap-short-relator-cylinders, fpbs-high-girth-uniform-l2-patch, fpbs-l2-gap-class-closed-under-local-limits]
artifacts:
  - research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md
---

SUFFICIENT route: Proposition 4.1 of
`research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`.

1. Write `X_{k,eta} = P_{k,eta} union union_{1 <= |w| < L(eta)} Z_{k,eta,w}`,
   a finite union. `P_{k,eta}` is the high-girth set.
2. `fpbs-high-girth-uniform-l2-patch` gives
   `P_{k,eta} subseteq U_{1+3/eta^2, eta/(4(2k-1))}`.
3. `fpbs-uniform-l2-gap-short-relator-cylinders` gives
   `Z_{k,eta,w} subseteq U_{M_w,delta_w}` for each of the finitely many `w`.
4. Put `M = max` and `delta = min` of the finitely many constants. By
   monotonicity (F1) of `fpbs-l2-gap-class-closed-under-local-limits`, every
   piece lies in `U_{M,delta}`.

The route is conditional: its content is the open cylinder claim.
