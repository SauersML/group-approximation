---
rg: 2
id: steinberg-pushed-marginal-sum-proof
kind: route
title: Telescope the pushed fiber equations around their fractional-linear orbits
target: steinberg-pushed-marginal-sums-have-no-new-closure
requires:
  - steinberg-fox-marginal-pushes-are-explicit
---

Let `eta=1/2`.  Summing the point push of `Xf=0` first over `b` gives,
for `d_a=1-2a` and `a!=eta`,

```text
A(a)=A(a/d_a)-A(a/d_a+eta)-H(-eta,-2a)+H(0,-2a).    (SMS2)
```

At `a=eta` only the last two terms remain.  Dually, with
`gamma=c/[2(1-c)]` and `c!=1`, summing the plane push gives

```text
C(c)=-P(-eta,-c/2)+P(0,-c/2)+C(gamma)-C(gamma+eta).  (SMS3)
```

At `c=1` only the two `P` terms remain.  Summing either equation over the
complete fractional-linear orbit telescopes its translated difference.
The `u` cases `(SMP4)`--`(SMP5)` telescope to the same two boundary
balances because `C_((1-q)f)=T_((1-q)f)=0`.  Finally the total sum of the
first row is

```text
T=A(0)-A(-eta)+C(0)-C(-eta),                          (SMS4)
```

which is `(SMS1)`.  These calculations exhaust the unweighted full-fiber
and full-orbit sums of the pushed equations and yield no independent
absolute constraint on `P` or `H`.
