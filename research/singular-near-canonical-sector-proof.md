---
rg: 2
id: singular-near-canonical-sector-proof
kind: route
title: Identify the cyclic trace sector and kill every translated near defect
target: singular-near-defects-vanish-on-canonical-genuine-sector
requires:
  - invariant-free-near-state-is-amenable-regular-cover
---

Let `(K_phi,sigma,Omega)` be the GNS representation of `phi`.  For `a in A`,

```text
||sigma(a)Omega||^2=phi(a^*a)=tau(a^*a).                (SNCP1)
```

Hence the map `a -> sigma(a)Omega` identifies `K_A` with `L^2(A,tau)`, or
equivalently with `L^2(A/I_tau,bar tau)`.  Since `tau` is tracial,
`I_tau` is a closed two-sided ideal.  The near-representation identities give

```text
d(g,h) in I_tau.                                       (SNCP2)
```

Left multiplication by `pi(g)` preserves `(SNCP1)`, so `K_A` is invariant
and `rho(g)=sigma(pi(g))|_(K_A)` is unitary.  For `a in A`, two-sidedness of
`I_tau` gives `d(g,h)a in I_tau`, and therefore

```text
(rho(g)rho(h)-rho(gh))sigma(a)Omega
 =sigma(d(g,h)a)Omega=0.                               (SNCP3)
```

The vectors `sigma(a)Omega` are dense in `K_A`, proving that `rho` is a
genuine representation.  The quotient identification from
`invariant-free-near-state-is-amenable-regular-cover` gives `(SNG4)` and its
regular-character specialization.

For `a,b in A`, `(SNCP2)` and two-sidedness also give

```text
a d(g,h)b in I_tau,
||sigma(a d(g,h)b)Omega||^2
 =tau(b^*d(g,h)^*a^*a d(g,h)b)=0.                      (SNCP4)
```

This proves `(SNG5)`, and continuity kills every `L^2(tau)` limit of finite
linear combinations of translated defects.

Finally, on the full GNS space the group-law difference is exactly
`sigma(d(g,h))`.  The near identity proves it kills `Omega`, but its value on
`sigma(T)Omega` has squared norm

```text
phi(T^*d(g,h)^*d(g,h)T),                               (SNCP5)
```

which is not controlled by `phi(d(g,h)^*d(g,h))=0` for arbitrary
`T in B(H)`.  This proves the stated separation between the canonical genuine
sector and the remaining singular directions.
