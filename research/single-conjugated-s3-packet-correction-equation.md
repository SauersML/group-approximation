---
rg: 2
id: single-conjugated-s3-packet-correction-equation
kind: claim
title: The concrete corner lifts reduce a one-packet correction to one finite equation
distinct_from:
  leavitt-recursive-kernel-idempotents: that iterates locally finite kernel packets and never terminates; this uses one conjugate of the original S3 additive kernel relation and no recursive tower.
  leavitt-rank-three-lift-has-no-one-sided-inverse: that excludes the unmodified rank-three corner lift; this writes the exact modification that must leave its virtually free support subgroup.
  leavitt-corner-one-sided-lift-exists: that quantifies over arbitrary corner elements; this pins explicit lifts, an explicit finite defect, and one group-unit parameter.
artifacts:
  - research/artifacts/one-nonnormal-packet-corner-correction-2026-08-21.md
---

Let `t~,s~` be the explicit three-unit lifts, `A=e t~ e`, `B=e s~ e`, and
`Delta=AB+e`.  The whole-algebra defect `D=t~s~+1` has support exactly ten,
and

```text
Delta=e D e + e t~(1+e)s~e.
```

For the constant `S_3` kernel relation `k=[u]+[v]+[w]` and any `x in R^x`,
put `P_x=e[x]k[x^-1]e`.  Then `P_x in ker(pi_e)`, and the modified lift
`A_x=A+P_x` gives the required direct-finiteness witness with the fixed `B`
if and only if

```text
P_x B=Delta.
```

This is an explicit finite one-nonnormal-packet equation.  No solution `x`
is currently known; any solution must escape every support subgroup whose
`F_2` group algebra is known directly finite.

## Attempts

The original `S_3` packet gives zero because `ek=ke=0`.  Conjugating inside
its normalizer remains trapped in finite packet algebra.  The first viable
attack is therefore to choose `x` outside that normalizer and compare the
finite supports in the displayed equation; this audit derives the equation
but does not find such an `x`.

