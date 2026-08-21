---
rg: 2
id: all-abelian-uniform-hs-rounding-proof
kind: route
title: Apply uniform HS stability to the class of abelian groups
target: all-abelian-uniform-hs-rounding-gives-global-pvm
requires: []
---

Akhtiamov--Dogon Theorem 3.2(1) states that, for every integer `r`, the
class of amenable groups all of whose finite-dimensional irreducible unitary
representations have dimension at most `r` is uniformly HS-stable.  The
definition is exactly an all-pairs epsilon-homomorphism with sup-norm
closeness on the whole source group, and the correcting representation has
the same matrix dimension.  Take `r=1`.  Every countable abelian group lies
in that class, giving `(AUR1)`--`(AUR2)` with one group-independent modulus.

For an elementary abelian two-group, every exact representation is a direct
sum of characters valued in `{+1,-1}`.  Group equal character summands to
obtain the finite-support PVM `(AUR3)`.  The actor-covariance estimate is the
triangle inequality applied before and after conjugation, using the uniform
closeness in `(AUR2)`.

