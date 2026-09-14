---
rg: 2
id: leavitt-surjunctivity-tower-proof
kind: route
title: Compose the Thompson-in-Leavitt embedding with the d-ary corner embedding, then apply subgroup heredity
target: leavitt-surjunctivity-tower
requires:
  - surjunctivity-passes-to-subgroups
  - leavitt-cylinder-swaps-generate-thompson-in-el
  - leavitt-gl-equals-el-and-perfect-unit-group
  - d-ary-leavitt-groups-nonsofic-over-finite-fields
artifacts:
  - research/artifacts/gottschalk-other-hosts-2026-09-12.md
---

## Direct proof

Write `R = L_{F_2}(1,2)`, `R^x = R^x`, `A^x = L_{F_2}(1,d)^x`, `d >= 2`.

**Step 1: `V <= R^x`.** By `leavitt-cylinder-swaps-generate-thompson-in-el`,
Thompson's `V <= EL_D(R) =~ EL_9(R)` for the complete nine-leaf code `D`. By
`leavitt-gl-equals-el-and-perfect-unit-group`, `GL_n(R) = EL_n(R)` for every
`n >= 2`, and prefix-code self-similarity identifies all these with the unit
group `R^x` (the three-leaf code gives `R^x = GL_3 = EL_3`). Hence `V <= R^x`.

**Step 2: `R^x <= A^x`.** By `d-ary-leavitt-groups-nonsofic-over-finite-fields`
and its corner route, the corner of `L_{F_2}(1,d)` at `e = p_0 + ... + p_{d-2}`
carries a unital binary Leavitt family. Over `F_2` the subalgebra it generates is
a copy of `L_{F_2}(1,2)` (a Leavitt algebra `L(1,2)` is simple, so its family
generates exactly it), and the corner-extension homomorphism on units is
injective. Hence `R^x <= A^x`.

**Step 3: monotonicity.** Apply `surjunctivity-passes-to-subgroups` to the chain
`V <= R^x <= A^x`. Surjunctivity descends along inclusions and non-surjunctivity
ascends. This gives both displayed implication chains.

No step decides surjunctivity of any of the three groups; the route only assembles
the inclusions and applies heredity. The consequences (the FP simple nonsofic
group is `R^x`; a non-surjunctive `V` is nonsofic) are immediate from Step 1 and
Gromov--Weiss.
