---
rg: 2
id: leavitt-units-span-every-d-ary-leavitt-algebra
kind: claim
title: Units additively span every ring with a unital d-ary Leavitt family, so every finite-field Leavitt group algebra surjects onto its algebra
distinct_from:
  leavitt-unit-group-algebra-surjects-onto-leavitt: that is the binary case, machine-checked for rings carrying a unital binary Leavitt family; this covers every arity d >= 2 on paper. For d >= 3 the algebra L_(F_q)(1,d) has module type (1, d-1), so it is not isomorphic to its square as a module and carries no unital binary family, and that claim does not apply.
artifacts:
  - research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md
---

Let `R` be a unital ring carrying a unital `d`-ary Leavitt family `s_1, ..., s_d, t_1, ..., t_d`,
with `t_i s_j = delta_ij`, `sum_i s_i t_i = 1` and `d >= 2`. Then the additive subgroup generated
by the units of `R` is all of `R`.

**Consequence.** For every prime power `q` and every `d >= 2`, the evaluation

    pi : F_q[L_(F_q)(1,d)^x] -> L_(F_q)(1,d)

is surjective. For `lambda` in `F_q^x` and a unit `u`, `lambda u` is a unit, so the `F_q`-span of the
units equals their additive span. So every element of the Leavitt algebra, including every
image-level corner solution, has preimages in the group algebra, and since `pi` kills the other
scalar factors, in the Leavitt-visible factor
(`leavitt-unit-group-algebras-split-over-scalar-characters`).

ESTABLISHED by `d-ary-leavitt-unit-span-proof`.
