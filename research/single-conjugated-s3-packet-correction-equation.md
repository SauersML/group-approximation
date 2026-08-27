---
rg: 2
id: single-conjugated-s3-packet-correction-equation
kind: claim
title: The concrete one-sided packet correction equation has no solution
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

This explicit equation has no solution.  The fixed right factor `B` lies in
the corner over its virtually free support group `K_s`; a solution would give
`B` a left inverse in the ambient corner.  Coset projection and direct
finiteness of `F_2[K_s]` would make `B` two-sided invertible, making its image
`s_0` a unit, which it is not.

## Attempts

The original `S_3` packet gives zero because `ek=ke=0`, suggesting an outside
conjugator.  The support-localization argument above supersedes that search:
even an arbitrary outside conjugator cannot repair only the left factor.
