---
rg: 2
id: unitary-loop-detection-from-lxi
kind: route
title: LXI applied to C(T, D) detects unitary loops by their K1(SD) class
target: properly-infinite-unitary-loops-detected-by-k1-suspension
requires: [stw99-problem-lxi-properly-infinite-k1-injective]
artifacts:
  - research/artifacts/lxi-quotient-minimal-counterexamples-2026-09-16.md
---

Let `D` be unital and properly infinite, and `l` a based loop in `U(D)` with trivial class `kappa_D(l)` in
`K_1(SD)`.

1. `C(T, D)` contains the constants `D` unitally, so it is unital and properly infinite. Via
   `T = [0,1]/{0,1}`, `l` is a unitary of `C(T, D)`.
2. The unital \*-homomorphism `j: (SD)~ → C(T, D)`, `x + λ1 ↦ x + λ1_D`, sends `1 + (l − 1)` to `l`. So
   `[l]_{K_1(C(T,D))} = j_*(kappa_D(l)) = 0`.
3. LXI makes `C(T, D)` K1-injective, so `l ∈ U_0(C(T, D))`. A norm-continuous path `λ ↦ H_λ` in `U(C(T, D))`
   from `l` to 1 is a jointly continuous map `T × [0,1] → U(D)`.
4. `(z, λ) ↦ H_λ(z) H_λ(1)^{-1}` is still continuous, equals `l` at `λ = 0` (because `l(1) = 1`), equals 1
   at `λ = 1`, and equals 1 at the base point `z = 1`. It is a null-homotopy of `l` relative to `{0, 1}`.
