---
rg: 2
id: simple-torsion-macroscopic-mf-dichotomy-proof
kind: route
title: Combine simplicity of the radical with torsion active-core reblocking
target: simple-torsion-groups-have-a-macroscopic-mf-dichotomy
requires:
  - countable-mf-groups-are-epireflective
  - torsion-normal-generator-has-full-support-corona-core
---

The MF radical is a normal subgroup.  Simplicity therefore makes it either
`1` or `G`.  In the second case every corona homomorphism is trivial.

In the first case the MF reflection is `G`, so `G` is MF and has a faithful
corona representation.  Enlarge a finite generating set by `a`.  Since `G`
is simple, `a` normally generates every generator, and every nonidentity
element `g` normally generates `a`.  Apply torsion active-core reblocking.
It gives a stably equivalent operator-norm asymptotic representation in
which the active projection of `a` has a positive normalized rank lower
bound.  The normal-generation word from `g` to `a` and Hilbert--Schmidt
telescoping give a positive separation constant for each fixed `g`.

The reblocked model remains faithful because every nonidentity element has
positive Hilbert--Schmidt, hence operator-norm, distance from the identity.
Conversely, any faithful operator-norm asymptotic model defines an injective
norm-corona homomorphism.  A nontrivial corona homomorphism from a simple
group is injective.  This proves all three equivalences.

If one uniform bound controls the number of conjugates needed to express
`a` from every `g!=1`, the telescoping constant is independent of `g`, giving
uniform separation.
