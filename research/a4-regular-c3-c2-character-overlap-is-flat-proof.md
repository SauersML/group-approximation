---
rg: 2
id: a4-regular-c3-c2-character-overlap-is-flat-proof
kind: route
title: Fourier expansion and C3 intersect C2 trivially leave only the identity coefficient
target: a4-regular-c3-c2-character-overlap-is-flat
requires: []
---

Write the character projections in the two cyclic subgroup algebras as

```text
P_chi=(1/3) sum_(r=0)^2 conjugate(chi(a^r)) rho(a^r),
Q_eps=(1/2) sum_(s=0)^1 conjugate(eps(b^s)) rho(b^s).
```

In a multiple of the regular `A4` representation,

```text
tau(rho(g)) = 1  if g=1,
              0  otherwise.
```

Therefore

```text
tau(P_chi Q_eps)
 = (1/6) sum_(r,s)
     conjugate(chi(a^r) eps(b^s)) tau(rho(a^r b^s)).
```

The subgroups `<a>` and `<b>` have coprime orders `3` and `2`, hence trivial
intersection.  Thus `a^r b^s=1` occurs only for `r=s=0`.  Exactly one summand
survives and it equals `1/6`, independently of `chi,eps`.

Since `tau(P_chi)=1/3` and `tau(Q_eps)=1/2`, dividing the joint weights by the
marginals gives the conditional probabilities `1/2` and `1/3`.  Hence the
associated `3 x 2` stochastic transition matrix has identical rows (and the
reverse channel identical rows as well), so it has rank one.