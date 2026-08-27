---
rg: 2
id: relative-fixed-algebra-payment-proof
kind: route
title: Project to the commutant, then expose the multiplicity-capture countermodel
target: relative-fixed-algebra-payment-lemma
requires:
  - finite-group-intertwiner-laplacian-gap
---

Because `E_N` is the orthogonal projection in `L^2(M_d)` and `p=p^*=p^2`,

```text
||p-E_Np||_2^2
 =||p||_2^2-||E_Np||_2^2
 =tau(p)-||E_Np||_2^2.
```

Equations `(RFA1)--(RFA3)` give `(RFA4)`, and `(RFA5)` gives the relator
floor. For a finite group, `E_N` is the Reynolds average

```text
E_N(p)=|H|^(-1) sum_h rho(h)p rho(h)^*.
```

Self-adjointness and idempotence of `E_N` give

```text
||E_Np||_2^2=<p,E_Np>
 =|H|^(-1)sum_h tau(p rho(h)p rho(h)^*),
```

which proves `(RFA6)`.

The criterion is sharp up to constants. Since `E_Np` commutes with `S`,

```text
sum_s||[s,p]||_2^2
 <=4|S| ||p-E_Np||_2^2.                                (RFA7)
```

In particular, take `rho=rho_0 tensor I_m` and
`p=I tensor q_m`, with `rank(q_m)/m->beta`. Then `p in N`, every commutator
energy is zero, and yet `tau(p)->beta`; `p` may have full central support and
be noncentral in the ambient matrix algebra. Positive carrier density,
character data, or an adjoint gap off `N` cannot distinguish this
multiplicity-reservoir capture.

The robust form is immediate: if

```text
||p-E_Np||_2^2 >= gamma tau(p)-eta_cap,
E_S(p) <= C E_rel+eta_bridge,
```

then

```text
E_rel >= [kappa(gamma beta-eta_cap)-eta_bridge]/C.
```

For several packet families with fixed algebras `N_i`, the same proof works
when their fixed subspaces have a uniform Friedrichs-angle bound

```text
dist_2(x, intersection_i N_i)^2
 <= Lambda sum_i dist_2(x,N_i)^2.
```

The combined gap is `(min_i kappa_i)/Lambda`, but the carrier must still
avoid the joint commutant. Multiple expanders whose joint commutant retains
the multiplicity reservoir do not spread any error.
