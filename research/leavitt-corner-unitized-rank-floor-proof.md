---
rg: 2
id: leavitt-corner-unitized-rank-floor-proof
kind: route
title: Add the complementary idempotent and apply the universal modular rank-pair bounds
target: leavitt-corner-witness-has-unitized-rank-floor
requires:
  - dykema-heister-juschenko-bounded-rank-direct-finiteness
artifacts:
  - research/artifacts/leavitt-corner-unitized-rank-floor-2026-08-21.md
---

Because `z=1-e` is orthogonal to `e`, all cross terms vanish and

```text
alpha beta=ab+z=e+z=1,
beta alpha=ba+z!=1.
```

Augmentation gives `eps(alpha)eps(beta)=1`, so both augmentations are one and
their support sizes are odd.  Neither support can have size one.  For example,
if `alpha=[h]`, then `pi(alpha)=h` is a unit of `R`.  But
`pi(alpha)=pi(a)` because `pi(z)=0`; from `pi(a)pi(b)=1`, two-sided
invertibility of `pi(a)` would force `pi(b)=pi(a)^(-1)` and
`pi(ba)=1`, contrary to the witness condition.  The same argument applies to
`beta`.  Thus both ranks are odd and at least three.

Dykema--Heister--Juschenko direct finiteness for rank pairs `(3,n)`,
`n<=11`, excludes every profile with one rank three and the other at most
eleven.  Their `(5,5)` result excludes that remaining symmetric profile.
Ordering two odd ranks at least three leaves `(3,n)` with `n>=13`, or both
at least five but not `(5,5)`, whose smallest possibility is `(5,7)`.
