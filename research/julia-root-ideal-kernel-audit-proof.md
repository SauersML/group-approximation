---
rg: 2
id: julia-root-ideal-kernel-audit-proof
kind: route
title: Reduce dual-number coefficients while retaining the unit-root Julia commutator
target: one-julia-root-anchor-has-ideal-kernel-escape
requires: []
artifacts:
  - research/artifacts/s3-mixed-root-julia-ideal-audit-2026-08-23.md
---

The map `F_5[eps]/(eps^2)->F_5` is a unital ring quotient, so applying it
entrywise proves `(JIK1)` and preserves every Steinberg relation.

Write `c=x_13(1)` in `UT_3(F_5)`.  The automorphism interchanging `x_12`
and `x_23` sends `c` to `c^(-1)`.  If `z` implements this automorphism and

```text
j=z c^3,
```

then `j^2=1` and

```text
zjzj=c^6=c
```

because `c` has order five.  This proves `(JIK2)`.  Since `c` is nonidentity,
its left-regular trace is zero.  The exact two-reflection identity from
`free-julia-grading-carries-one-gram-at-canonical-quarter-mass` gives Julia
off-diagonal mass `1/4`.

The scalar endpoint substitution from
`s3-packed-root-retraction-audit-proof` proves `(JIK3)`.  Under the same
dual-number reduction the designated coordinate is identity, so its defect
is zero despite that positive row energy.

Finally set `j=z` after reduction.  Then `zjzj=1=x_13(eps)`, proving the
zero-carrier absorber for `(JIK4)`.  These computations establish both
proper-ideal and direct-Julia escapes.

