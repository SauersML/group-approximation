---
rg: 2
id: low-degree-invariant-output-reduces-to-corner-fullness-proof
kind: route
title: Invariant output makes the linear part left H-invariant, then augmentation or the averaging idempotent decides
target: low-degree-invariant-output-reduces-to-corner-fullness
requires:
  - low-degree-strict-pairs-have-one-sided-linear-parts
artifacts:
  - research/artifacts/low-degree-strict-pairs-linear-parts-2026-09-12.md
---

Section 3 of the artifact.

1. **Normalize.** Translation by the constant configuration `tau(0)` keeps the output
   invariant.
2. **Invariance.** For every `x`, the reduced local rule in the variables `x_(hs)` equals the
   rule in the variables `x_s`. Comparing linear coefficients gives `A_u = A_(h^-1 u)`, which is
   `h A = A`.
3. **Prerequisite.** It gives `C A = I_m`.
4. **Case `p` divides `|H|`.** The coefficients of `A` are constant on free left `H`-orbits, so
   `eps(A) = 0`, and `eps(C) eps(A) = I` is impossible.
5. **Case `p` does not divide `|H|`.** `e A = A`, so `C e A = I`. Conversely `C e B = I` makes
   `tau_(eB)` invariant, with decoder `tau_C`. Also `AC = I` would force `e = 1`.
6. **Prime field.** Restriction of scalars along the regular representation
   `F_q -> M_k(F_p)` embeds `M_m(F_q[G])` in `M_(mk)(F_p[G])` and fixes `e I`.
