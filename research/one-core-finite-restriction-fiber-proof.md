---
rg: 2
id: one-core-finite-restriction-fiber-proof
kind: route
title: Use the core unipotent order to capture every exact endpoint in one finite quotient
target: one-core-endpoint-union-is-one-finite-restriction-fiber
requires:
  - bs14-unitary-representations-are-periodic-cycle-packets
  - bounded-period-iwahori-quotients-are-finite
  - congruence-endpoint-orbits-are-restriction-ring-fibers
---

By `bs14-unitary-representations-are-periodic-cycle-packets`, the spectrum
of `beta(s)` is a finite union of finite fourth-power orbits.  Hence
`beta(s)` has finite odd order `N`.

If `pi` is an exact endpoint extending `beta`, then

```text
pi(s^N)=beta(s)^N=1.
```

The universal property of the quotient gives a unique factorization of
`pi` through `A_N`.  The converse is immediate by composing a representation
of `A_N` with the quotient map.  By
`bounded-period-iwahori-quotients-are-finite`, `A_N` is finite.

Decompose a representation of `A_N` into its irreducibles.  Its restriction
is `beta` exactly when its nonnegative multiplicity vector maps to `[beta]`
under restriction, proving `(OCF4)`.  Two such extensions differ by
core-commutant conjugacy exactly when their global `A_N` multiplicity
vectors agree, as in
`congruence-endpoint-orbits-are-restriction-ring-fibers`.  Finally, fixed
dimension bounds every multiplicity, so the nonnegative fiber is finite.

