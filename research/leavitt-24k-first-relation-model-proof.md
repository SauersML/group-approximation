---
rg: 2
id: leavitt-24k-first-relation-model-proof
kind: route
title: Telescope the cube-root word for the bound, then read the relation off F8 arithmetic
target: leavitt-24k-first-relation-has-exact-finite-model
requires: []
artifacts:
  - research/artifacts/leavitt-24k-relative-unitary-reduction-2026-09-08.md
---

## Proof

**Images.**  By the commutator rule `[x_ij(a), x_jl(b)] = x_il(ab)` and the
index shift under `c`, the images of `(LR1)` are `q(d) = x_13(1)`,
`q(a) = x_12(1)`, `q(b) = c x_13(1) c^(-1) = x_21(1)`, and
`q(z) = x_12(1) x_21(1) x_12(1) = (12)`.  Since `(12)c = (23)` has order two,
`q(r_*) = ((12)c)^2 = 1`.

**The bound.**  Write `D = pi(d)` and `Z = pi(z)`.  In the free product `z`
is conjugate to `b`, which is conjugate to `d`, so `||Z - I||_2 = ||D - I||_2`
before any relation is imposed.  Telescoping,

```text
|| Z C_k Z C_k - C_k^2 ||_2 <= 2 ||Z - I||_2,
```

and `tr(C_k^2) = 0` gives `||C_k^2 - I||_2 = sqrt 2`.  The triangle
inequality applied to `C_k^2 - I = (C_k^2 - Z C_k Z C_k) + (pi(r_*) - I)`
gives `(LR2)`, since `D = [pi(b_2), C_k pi(b_1) C_k^*]`.

**The exact model.**  `alpha^3 + alpha + 1` has no root in `F_2`, hence is
irreducible, and `alpha(alpha^2 + 1) = alpha^3 + alpha = 1`, so
`alpha^(-1) = alpha^2 + 1`.  In the basis `1, alpha, alpha^2` the vectors
`1, alpha, alpha^2 + 1` are independent, so `x_12(1), x_12(alpha),
x_12(alpha^(-1))` generate a group of order eight; `c` still has order three
and lies in `EL_3(F_8)`.  Repeating `(LR1)` with these coefficients,

```text
d = [x_12(alpha^(-1)), x_23(alpha)] = x_13(alpha^(-1) alpha) = x_13(1),
```

after which the computation is identical to the one above and `r_* = 1`
exactly in `GL_3(F_8)`.

Take the left regular representation of the finite group `G = GL_3(F_8)`.
Restricted to any subgroup it is a direct sum of copies of that subgroup's
regular representation, because left translation partitions `G` into cosets.
Hence both `<c>` and the order-eight group appear with exactly regular
multiplicities, and `|G| = (8^3-1)(8^3-8)(8^3-8^2) = 115379712` is `24` times
`4807488`.  Matching simultaneous eigenspaces as in
`binary-leavitt-24k-criterion-proof` puts this into the frozen form with a
single relative unitary and `pi(r_*) = I`.

**Why it is not a model of `H`.**  Completing the coefficient assignment
through `(LG2)` would need `v s_0 = s_1` and `t_0 v = t_1` with
`s_0 = alpha`, `t_0 = alpha^(-1)`, `v = 1`, giving `s_1 = s_0` and
`t_1 = t_0`, which contradicts `t_0 s_1 = 0` against `t_0 s_0 = 1`.
