---
rg: 2
id: simple-ring-el3-lef-forces-lef-ring
kind: claim
title: Every countable simple ring whose rank-three elementary group is LEF is a LEF ring
distinct_from:
  simple-ring-with-matrix-units-el-lef-iff-matricial: that proves the rank-two and rank-three converse for simple rings containing nonzero 2x2 matrix units; this asks for it for every simple ring, where the open case is rings without such matrix units.
---

**OPEN.** Let `R` be a countable simple unital ring with `EL_3(R)` LEF. Is `R` a LEF ring, equivalently exactly
matricial over finite fields (`simple-lef-rings-are-exactly-matricial`)?

Known cases:
- rank at least four: `lef-elementary-groups-force-lef-rings`;
- simple rings with nonzero 2x2 matrix units, at every rank `N >= 2`: `el-lef-with-full-matrix-units-forces-lef-ring`
  and `simple-ring-with-matrix-units-el-lef-iff-matricial`.

So the open case is simple rings with no nonzero 2x2 matrix units, such as division rings, simple domains, and simple
rings whose nontrivial idempotents admit no orthogonal equivalent pair.

## Attempts

- **The finitely presented Steinberg cover dies at rank three.** `St_3(A)` over a free ring `A` is not finitely
  presented, since `A` maps onto `F_p[t]` (Krstić–McCool Cor. 2, as quoted by Ershov–Jaikin-Zapirain). So a partial
  model of a ball of `EL_3(R)` need not extend to a homomorphism `St_3(A) -> Q`, and the level ideal is undefined.
- **The matrix-unit corner needs nonzero matrix units** (`el-lef-with-full-matrix-units-forces-lef-ring`). A domain has
  none: `ε_12^2 = 0` forces `ε_12 = 0`, so `ε_11 = ε_12 ε_21 = 0`.
- **Full complementary idempotents: untried route.** If `R` has an idempotent `e != 0, 1`, simplicity makes `e` and
  `1 - e` full, and `EL_3(R)` contains the six block subgroups `I + E_A M_3(R) E_B` for the blocks `e E_pp` and
  `(1-e) E_pp`, as in `complementary-full-idempotents-make-el-2-kazhdan`. A Krstić–McCool-type finite presentation
  of the graded Steinberg group over a free ring with a complete system of six full orthogonal idempotents would run
  the level-ideal argument at rank three for every simple ring with a nontrivial idempotent. No such presentation
  theorem is on main.
- **Calibration for domains.** Fields and the Weyl algebra `A_1(Q)` are LEF rings with LEF `EL_3`, by Malcev and
  `weyl-algebra-over-q-is-lef-ring-not-matricial-over-q`. Consistent.
  - A counterexample must be a simple domain `D` with `EL_3(D)` LEF but `M_m(D)` not LEF for some `m`, e.g. `M_2(D)`
    not directly finite.
  - The non-MF full-complementary-idempotents theorem then kills `EL_n(M_2(D)) = EL_(2n)(D)`, `n >= 2`, so it
    decides ranks at least four and leaves rank three untouched.
