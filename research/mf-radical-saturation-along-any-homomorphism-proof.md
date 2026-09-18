---
rg: 2
id: mf-radical-saturation-along-any-homomorphism-proof
kind: route
title: Functoriality pushes the word forward; normality of the radical does the rest
target: mf-radical-saturation-along-any-homomorphism
requires:
  - mf-radical-functoriality
---

By `mf-radical-functoriality`, `f(Rad_MF(E)) <= Rad_MF(Q)`, so
`f(d) in Rad_MF(Q)`.  The MF radical is the intersection of kernels of maps
to MF groups, so it is normal.  Hence it contains `normalClosure_Q(f(d))=Q`.
Also `f(d)!=1` makes `Q` nontrivial.

Now let `pi:Q->>L` be a nontrivial quotient.  Functoriality for `pi` gives
`L=pi(Q)=pi(Rad_MF(Q)) <= Rad_MF(L)`.

The proof of `torsion-free-mf-radical-routing-saturation` is this argument;
it never uses surjectivity of the routing map.
