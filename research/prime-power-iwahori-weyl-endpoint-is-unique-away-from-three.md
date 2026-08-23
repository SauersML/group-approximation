---
rg: 2
id: prime-power-iwahori-weyl-endpoint-is-unique-away-from-three
kind: claim
title: The standard prime-power Iwahori Weyl group element is unique away from three
distinct_from:
  prime-field-iwahori-weyl-endpoint-is-unique-away-from-three: that is the residue-field calculation; this includes every depth over Z modulo p to the k and handles the exceptional negative-lift branch at p=5.
  congruence-iwahori-endpoint-fiber-contains-core-commutant-orbits: this uniqueness concerns elements of the finite congruence group itself; that theorem shows the endpoint fiber in a unitary representation is nevertheless large because of multiplicity commutants.
  odd-congruence-iwahori-pairs-have-uniform-linear-repair: that is the full representation-level HS repair theorem; this removes only group-element label ambiguity on one fixed standard core.
---

Let `p>3` be prime, `k>=1`, and work in
`PSL_2(Z/p^k Z)`.  On the standard square-free core

```text
r=h(2)=diag(2,2^(-1)),       t=u(1)=[1 1;0 1],        (PPU1)
```

the standard Weyl element `w=[0 -1;1 0]` is the unique **group element**
`x` satisfying

```text
x^2=1,       xrx=r^(-1),       (xt)^3=1.              (PPU2)
```

Thus the second cubic is unnecessary for exact Weyl-label uniqueness on
every standard prime-power core away from three.  The excluded prime is
structural: `2-2^(-1)=3/2` ceases to be a unit, so inversion no longer
forces a clean Weyl-normalizer coset.

This does not make the representation endpoint fiber unique.
`congruence-iwahori-endpoint-fiber-contains-core-commutant-orbits` gives
many exact endpoint matrices over the same represented core at every finite
level.  Hence prime-power arithmetic removes a discrete group-element
ambiguity but leaves exactly the continuous multiplicity-commutant orbit
which the regular basin theorem must synchronize.

