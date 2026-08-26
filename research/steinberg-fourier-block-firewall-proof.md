---
rg: 2
id: steinberg-fourier-block-firewall-proof
kind: route
title: Compute endpoint Fourier modes and the transverse frequency mixing
target: steinberg-ordinary-fourier-blocks-do-not-descend-mod-p
requires:
  - steinberg-x-plus-incidence-dual-is-surjective
  - steinberg-fox-chord-actions-are-explicit
---

Over a field `K` of characteristic different from `p`, fix an additive
character `psi` and put

```text
Fhat_xi(a,c)=sum_b psi(-xi b)F(a,b,c).
```

For the endpoint potentials in `(SXD2)`, direct substitution gives

```text
D^*(alpha,beta)^hat_xi(a,c)
   =U_xi(a)+psi(-xi ac)V_xi(c).                         (SFF2)
```

At `xi=0` these two summands intersect in the constants and have dimension
`2p-1`; at `xi!=0` their intersection is zero and their dimension is `2p`.
The complementary dimensions sum to
`(p-1)^2+(p-1)(p^2-2p)=p^3-2p^2+1`, as required for the circulation space.

However, away from the tree strata,

```text
tau_(A^(-1))(a,b,c)=(a/e,b/e,ec-2b),       e=1+2a,
tau_(B^(-1))(a,b,c)=(a/4+b/2,b/2,2c/(1+2c)).          (SFF3)
```

Thus the `(b,c)` transform of `L_(A^(-1))` sends frequencies
`(xi,eta)` to `(e xi+2 eta,eta/e)`, while the `(a,b)` transform of
`L_(B^(-1))` sends `(rho,xi)` to `(4rho,2xi-4rho)`.  The root differences
preserve the initial `b` frequency, but these two outer maps do not; the
exceptional strata add marginal terms as well.

Finally the modular group algebra identity `(SFF1)` gives
`(t-1)^p=0`.  There are no nontrivial `p`th-root character idempotents in
characteristic `p`.  Over the cyclotomic integers, the product of the
nonzero factors `1-zeta^xi` is `p`, so the denominators required to split
the nonzero frequencies are not units at `p`.  This proves both asserted
failures and the scoped invalidation.
