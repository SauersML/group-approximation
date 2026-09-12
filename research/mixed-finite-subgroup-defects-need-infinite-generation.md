---
rg: 2
id: mixed-finite-subgroup-defects-need-infinite-generation
kind: claim
title: Nested finite-subgroup idempotent defects need two subgroups generating an infinite group
distinct_from:
  lifted-trace-detects-finite-subgroup-projectives: that proves the lifted trace is positive on projectives induced from ONE finite subgroup, so a defect is not such a projective; this treats a defect built as a difference of nested idempotents drawn from TWO finite subgroups, and locates the only surviving case.
  leavitt-nested-idempotent-corner-module-equivalence: that asks for a module isomorphism between two explicitly constructed nested corners over the torsion-free group Q, refuted by cocenter coefficients; this is a general obstruction over the Leavitt unit group R^x, ruling out difference-of-nested-idempotent defects whenever the two finite subgroups generate a finite group.
artifacts:
  - research/artifacts/mixed-finite-subgroup-defects-2026-09-12.md
---

Let `p` be prime, `G` a group, and `H_1, H_2 <= G` finite subgroups. Let
`e in M_n(F_p[H_1])` and `f in M_n(F_p[H_2])` be idempotents with `f <= e` and
`f != e` (that is `ef = fe = f`), and suppose the nonzero idempotent difference
`e - f` is a Kaplansky defect: `e - f = I_n - AB` for some `A, B in M_n(F_p[G])`
with `BA = I_n`.

*Amended 2026-09-12 after `w3-vf-linear` Section 9.1.* The hypothesis is `f != e`;
`f != 0` is not needed. With `f = e` the difference is `0 = I - AB` for `A = B = I`,
so that case must be excluded. With the amendment the claim is consequence 2 of
`lifted-trace-detects-finite-subgroup-projectives` applied at `H = <H_1, H_2>`.

**Claim.** If `H = <H_1, H_2>` is finite, no such configuration exists.

Consequently, for `G = R^x = L_(F_2)(1,2)^x`, any defect of the form `e - f`
with `e, f` supported in finite subgroups forces `<H_1, H_2>` to be infinite.
This is the only surviving shape of a difference-of-nested-idempotent defect,
and it complements the single-subgroup exclusion in
`lifted-trace-detects-finite-subgroup-projectives` (consequence 1) by handling
two subgroups.

## Why this shape

A Kaplansky counterexample for `R^x` is, up to the invisible normal form
(`leavitt-inverse-defects-are-visible-or-invisible`), a nonzero defect
idempotent `d = I - AB` with `BA = I`. The finite-subgroup route to building
one takes `d` from the abundant finite-subgroup idempotents of `F_2[R^x]`. A
single finite subgroup is already excluded, so the first open shape is a
difference `e - f` across two subgroups (`gk-l3-kernel`'s framing). This claim
removes the case where those two subgroups still lie in a common finite one.

## Proof

If `H = <H_1, H_2>` is finite then `e, f in M_n(F_p[H])`, so `e - f` is a
nonzero idempotent of `M_n(F_p[H])` with `f < e`. Its induced ambient
projective is
`(e - f) F_p[G]^n`, and `d = I - AB` is a defect module: `A` restricts to an
isomorphism `F_p[G]^n -> (AB) F_p[G]^n`, so `(AB) F_p[G]^n` is free of rank `n`
and `d F_p[G]^n` is its complement. The lifted trace
`t_p : K_0(F_p[G]) -> Z_p` is additive, and for finite `H` and an idempotent
`c in M_n(F_p[H])` it is positive:
`t_p([c F_p[G]^n]) = dim_(F_p)(c F_p[H]^n)/|H| > 0` when `c != 0`
(`lifted-trace-detects-finite-subgroup-projectives`, LFT1). Hence

```text
t_p([d F_p[G]^n]) = t_p([(e - f) F_p[G]^n]) > 0
```

because `e - f` is a nonzero idempotent of the single finite group algebra
`M_n(F_p[H])` (as `f < e`). But a defect module
has `t_p = 0`: `d = I - AB` with `BA = I` gives
`[d F_p[G]^n] = [F_p[G]^n] - [(AB) F_p[G]^n] = 0` in `K_0`, since both are free
of rank `n` (`AB` is idempotent and `A` trivialises its range). So
`t_p([d F_p[G]^n]) = 0`, contradiction. QED

## Attempts

The infinite-generation survivor is open. Over `R^x` two finite subgroups
generically generate an infinite, often dense, subgroup, so this claim does
not by itself close the finite-subgroup route. What it removes is any hope of a
defect assembled inside one finite group: a witness must place `e` and `f` in
finite subgroups whose join is infinite, and then `t_p` is no longer computed
by the single-group formula LFT1. The lifted trace of an idempotent supported
in an infinite subgroup is not given by any finite-group dimension count, and
positivity there is exactly what
`lifted-trace-detects-finite-subgroup-projectives` does not assert. A separate
invariant, or the compression structure, is needed for that case.
