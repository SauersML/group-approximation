---
rg: 2
id: rationalizing-an-abelian-kernel-restores-torsion
kind: claim
title: Dividing a torsion-free abelian kernel gives every finite-order element downstairs a lift of the same order
distinct_from:
  free-abelianized-cover-is-torsion-free: that proves the relation cover is torsion-free as it stands; this shows that enlarging its abelian kernel to a rational vector space destroys exactly that property.
  torsion-free-central-cover-forces-abelian-finite-subgroups: that obstructs central covers through a finite-subgroup constraint on the base; this obstructs one specific repair operation on an arbitrary abelian-kernel extension and needs no centrality.
  integral-group-ring-congruence-groups-are-torsion-free-mf: that rules out a family of constructions by proving their outputs MF; this rules out one operation by proving its output has torsion.
artifacts:
  - research/artifacts/torsion-free-cover-perfect-and-congruence-obstructions-2026-09-08.md
---

**ESTABLISHED.**  Let `1 -> A -> E -> G -> 1` have torsion-free abelian
kernel, and push the kernel inclusion out along `A -> V = A tensor_Z Q`,
giving `E_Q = (V semidirect E)/D` with `D = {(-a,a) : a in A}`.  Then `V` and
`E` both inject into `E_Q`, the quotient of `E_Q` by `V` is `G`, and

```text
every g in G of finite order m has a lift of order exactly m.     (RK1)
```

Explicitly, if `e` maps to `g` and `e^m = a in A`, then
`e-tilde = (-a/m)e` has `e-tilde^m = 1`, the two factors commuting because
`e` centralizes `a = e^m`.

**Consequence.**  Rationalizing the abelian kernel of a torsion-free cover
over a base with torsion produces a group that is **not** torsion-free.  So
this operation is not available as a repair, and in particular it cannot be
used to make the abelian kernel divisible while keeping the cover
torsion-free.

No MF permanence is claimed for the pushout, in either direction.

DERIVATION
rationalized-kernel-torsion-lift-proof
