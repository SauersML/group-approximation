---
rg: 2
id: finite-character-idempotents-have-exact-hnn-transport
kind: claim
title: Matched finite-subgroup character idempotents have exact HNN transport
distinct_from:
  piecewise-group-transport-gives-corner-unitaries: that assembles a corner unitary after group conjugators for projection pieces are known; this supplies those conjugators from finite-subgroup character data and an ordinary group presentation.
  first-cycle-signed-hecke-chord: that must finish a no-CE atlas and therefore cannot remain in the residually finite finite-edge HNN class; this records the exact local transport that such an HNN extension does provide.
---

Let `H,L` be finite subgroups of a group `Gamma`, let
`phi:H -> L` be an isomorphism, and let `chi` be an irreducible character of
`H`.  Put `psi=chi circle phi^(-1)` and let

```text
z_(H,chi)=dim(chi)/|H| sum_(h in H) chi(h^(-1))h,
z_(L,psi)=dim(psi)/|L| sum_(l in L) psi(l^(-1))l.        (FHI1)
```

In the HNN extension

```text
Gamma_phi=<Gamma,t | t h t^(-1)=phi(h), h in H>,         (FHI2)
```

the base group embeds and

```text
t z_(H,chi) t^(-1)=z_(L,psi).                            (FHI3)
```

More generally, suppose in a corner with unit `q` the positive and negative
spectral projections of two separator-compatible involutions have finite
orthogonal decompositions

```text
e_s(1+epsilon X)/2=sum_k p_(s,epsilon,k),
e_s(1+epsilon Z)/2=sum_k r_(s,epsilon,k),                (FHI4)
```

where every matched pair is a finite-subgroup character idempotent related
as in `(FHI1)`.  Adjoin one stable letter for every pair and set

```text
V=sum_(s,epsilon,k) t_(s,epsilon,k) p_(s,epsilon,k).     (FHI5)
```

Then `V` is an algebraic finite-support corner unitary, it commutes with every
separator atom `e_s`, and

```text
V X V^*=Z.                                               (FHI6)
```

Thus finite character-idempotent resolution is an exact sufficient condition
for an algebraic relative-commutant regauge.  It is not sufficient for the
no-CE programme globally because finite-edge HNN extensions preserve residual
finiteness in the present base group.
