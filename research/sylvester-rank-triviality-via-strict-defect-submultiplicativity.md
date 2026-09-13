---
rg: 2
id: sylvester-rank-triviality-via-strict-defect-submultiplicativity
kind: route
title: A strict Sylvester-form deficit contradicts near-minimal multiplicativity, so every Sylvester rank function on the binary Leavitt unit group algebra kills the two-root defect
target: sylvester-rank-functions-on-leavitt-units-kill-two-root-defect
requires:
  - sylvester-disjoint-cylinder-defects-strictly-submultiplicative
  - sylvester-near-minimal-leavitt-defects-are-multiplicative
  - sylvester-leavitt-defect-gap-and-geometric-descent
artifacts:
  - research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md
---

## Why sufficient

Artifact Section 4.1. This is the class-(A) form of `leavitt-rank-triviality-via-strict-defect-submultiplicativity`.

1. **Positive infimum.** Suppose a non-augmentation Sylvester rank function exists. Then `c_*^Syl = inf rho_omega(D_1000)`
   is taken over a nonempty set, and it is at least `c_0 > 0` (`sylvester-leavitt-defect-gap-and-geometric-descent`).
2. **Near-minimizer.** Choose `rho` with `delta = rho_omega(D_1000) <= (1 + eps) c_*^Syl`. For disjoint proper
   cylinders `A`, `B` with proper union, `rho_omega(D_A D_B) >= delta^2 - 2 eps delta`
   (`sylvester-near-minimal-leavitt-defects-are-multiplicative`).
3. **Contradiction.** The deficit gives `rho_omega(D_A D_B) <= theta delta^2`, so `(1 - theta) delta <= 2 eps`. That
   fails once `eps < (1 - theta) c_0 / 2`. So the augmentation rank is the only Sylvester rank function, and it kills
   `D`.
