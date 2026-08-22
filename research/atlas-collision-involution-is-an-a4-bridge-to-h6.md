---
rg: 2
id: atlas-collision-involution-is-an-a4-bridge-to-h6
kind: claim
title: The collision involution is a regular-A4 bridge from the blind K line to the other H6 component
artifacts:
  - experiments/atlas_a4_19243_component_localization.py
distinct_from:
  atlas-a4-19243-s3xs3-localization: that identifies the commuting S3 times S3 collision cell on the large packet component; this computes the opposite incidence with the order-three line of the other rank-three packet component.
  atlas-a4-two-c3-line-carriers-have-exact-angle-gap: that computes the angle between the two fixed C3 carriers inside GL3(2); this identifies the moving regular-A4 carrier attached to the collision involution before that fixed-carrier angle can be used.
---

Let `H_6,K ~= S3` be the two components of the fourteen-word rank-three
packet core, let

```text
C_6 triangleleft H_6,       C_K triangleleft K
```

be their order-three subgroups, and let `b_0` be the repeated first-chart
involution in collision `19243`.  Exact closure in the stored `GL_4(F2)`
chart gives the asymmetric pair of incidences

```text
[b_0,K]=1,                                               (A4-BRIDGE-1)
<C_6,b_0> ~= A4.                                        (A4-BRIDGE-2)
```

More precisely, `b_0` does not normalize `C_6`, the group in
`(A4-BRIDGE-2)` has order distribution

```text
order 1: 1,       order 2: 3,       order 3: 8,
```

and

```text
<C_6,b_0> intersect H_6 = C_6,
<C_6,b_0> intersect K = 1.                              (A4-BRIDGE-3)
```

The closure with the full opposite component is also exact:

```text
S=<H_6,b_0> ~= S4,
S intersect <H_6,K> = H_6,
S intersect K = 1,                                    (A4-BRIDGE-4)
|<H_6,K,b_0>|=1344.                                   (A4-BRIDGE-5)
```

The order distribution in `S` is `1,9,8,6` in orders `1,2,3,4`, respectively.
Thus the moving carrier is equivalently the restriction of one fixed regular
`S4` packet to its point-stabilizer `H_6 ~= S3`.  The common-`U` compression
gate is a finite `S4 downarrow S3` branching problem coupled to the disjoint
`K` margin; no larger part of `A8` is needed to state it.

Thus the collision's continuous trivial/sign angle is not merely adjacent to
the other packet component: its repeated involution is already the reflection
of a named regular `A4` context with the other component's `C_6`.

This gives an exact common-`U` carrier reduction.  Put

```text
c(U)=U^* rho(b_0) U,
P_6(U)=U^* P_6 U.
```

Then `(P_6(U),c(U))` is the conjugate of the fixed regular-`A4` pair
`(P_6,rho(b_0))`.  Consequently the established `1` versus `1/3` spectral
split of `a4-regular-line-sector-spectral-split` applies to this **moving**
carrier with its full dimension-independent `2/3` gap, at every external
multiplicity.

The qualifier "moving" is load-bearing.  The angle estimate needed by
`atlas-a4-two-c3-line-carriers-have-exact-angle-gap` uses the fixed carrier
`P_6`, whereas ambient group identities alone canonically expose `P_6(U)`.
Therefore the remaining common-`U` compression problem can be stated more
narrowly: the `H_6` rectangle equations must transport the regular-`A4` line
carrier from `P_6(U)` to `P_6` on the canonical block

```text
Z(U)=E_K^- c(U) E_K^+.
```

This is a matrix/CE-sensitive transport statement.  It is not supplied by the
finite subgroup incidence, and replacing `P_6(U)` by `P_6` without using the
common packet equations would discard exactly the common-`U` gate.
