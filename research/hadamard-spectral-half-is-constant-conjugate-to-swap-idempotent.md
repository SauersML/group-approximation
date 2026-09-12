---
rg: 2
id: hadamard-spectral-half-is-constant-conjugate-to-swap-idempotent
kind: claim
title: The F_9 Hadamard spectral half is the swap idempotent conjugated by a constant unit of the anti-central summand
distinct_from:
  f9-hadamard-spectral-idempotents-are-half-idempotents: that shows f_+ and f_- are conjugate halves of the unit carrying a copy of M_2(F_9); this shows f_+ is conjugate, by an explicit unit supported on finitely many constant group elements, to the swap idempotent e_- itself.
  hadamard-unit-conjugates-swap-idempotent-to-cylinder: that conjugates e_- by the group element h to the cylinder idempotent q_[0] over F_3; this conjugates e_- to the non-rational spectral idempotent 2(1 + i[h]) of h over F_9, through the constant c and a unit of the dihedral subalgebra.
artifacts:
  - research/artifacts/hadamard-spectral-conjugacy-and-forced-states-2026-09-12.md
---

**ESTABLISHED** (proof: route `hadamard-spectral-half-constant-conjugacy-proof`; verification requested from
`w3-vf-linear`).

Let `R = L_(F_3)(1,2)`, `G = R^x`, `S_-^(9) = eps_- F_9[G]`, `e_- = 2 eps_-(1 + [w])` with
`w = s0 t1 + s1 t0`, and `f_+ = 2(1_- + i[h])` with `h = s0 t0 + s0 t1 + s1 t0 - s1 t1`. Put

```text
c = -s0 t0 + s1 t0 + s1 t1,     q = [c] e_- [c]^(-1) = 2 eps_- (1 + [hu]),     u = s0 t0 + s1 t0 - s1 t1,
v = f_+ q + (1_- - f_+)(1_- - q).
```

Then:
1. `c` is a constant involution of `G` with `c d c = u`, `c (wd) c = h` and `c w c = hu`, where `d = s0 t0 - s1 t1`.
2. `v` is a unit of `S_-^(9)`, with inverse `-(q f_+ + (1_- - q)(1_- - f_+))`, supported on the dihedral group
   `<h, u>` of order eight.
3. `f_+ = W e_- W^(-1)` with `W = v [c]`.

Consequently `c' f_+ b = 1_-` iff `(c' W) e_- (W^(-1) b) = 1_-`, so
`f9-hadamard-spectral-idempotent-is-full` is equivalent to `ternary-anti-invariant-swap-corner-is-full`
(routes `f9-hadamard-fullness-from-swap-corner-fullness` and the existing chain through
`hadamard-spectral-fullness-gives-f9-cohn-family`). The F_9 Hadamard line gains no room over the swap corner.
