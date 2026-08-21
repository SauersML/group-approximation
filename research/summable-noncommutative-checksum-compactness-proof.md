---
rg: 2
id: summable-noncommutative-checksum-compactness-proof
kind: route
title: Compactify bounded matrix tuples modulo simultaneous conjugacy and swap two nearby types
target: noncommutative-checksum-misses-bounded-types
requires: []
---

Equip the set of unitary-equivalence classes of `k`-dimensional unitary
representations with the pseudometric

```text
d([rho],[sigma])^2
 = inf_(V in U(k)) sum_n a_n
     ||rho(m_n)-V sigma(m_n)V^*||_(2,k)^2.              (1)
```

This pseudometric space is totally bounded.  Indeed, choose `N` so that
`4 sum_(n>=N)a_n<eta^2/2`.  The first `N` coordinates lie in the compact
space `U(k)^N`, whose quotient by simultaneous conjugacy is compact.  A
finite sufficiently fine net for that quotient controls the first `N`
terms of `(1)`, while the omitted tail costs at most
`4 sum_(n>=N)a_n`.  Hence finitely many `eta`-balls cover all
`k`-dimensional representations.

An infinite subset of a totally bounded pseudometric space contains two
distinct elements at arbitrarily small distance.  Applying this to `Omega`
and then choosing a conjugator within the defining infimum proves `(SNC2)`.

After replacing `sigma` by `sigma'=Ad(V)o sigma`, define

```text
pi(m) = diag(rho(m),sigma'(m)),
C     = [[0,I],[I,0]].                                  (2)
```

Direct block multiplication gives

```text
C pi(m) C^*-pi(m)
 = diag(sigma'(m)-rho(m),rho(m)-sigma'(m)).             (3)
```

Normalized trace on two equal blocks turns `(3)` into the equality in
`(SNC4)`.  Since `rho` and `sigma'` are inequivalent irreducibles, their two
summands are distinct isotypic components of `pi`.  The swap exchanges the
corresponding projections.  Each projection difference has squared
normalized Hilbert--Schmidt norm `1`, proving `(SNC3)`.

Finally, a uniformly bounded collection of positive integer dimensions has
an infinite constant-dimension subcollection.  This proves the stated
bounded-dimensional extension.
