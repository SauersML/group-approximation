---
rg: 2
id: restricted-burnside-finiteness-citation
kind: route
title: Import the positive solution of the restricted Burnside problem
target: restricted-burnside-finiteness
requires: []
---

Literature import, not a derivation.

Zelmanov's theorems (the pro-`p` case for prime-power exponent, then the
general case) together with the Hall--Higman reduction and the
classification of finite simple groups give: for every `m, N` the class of
finite `m`-generated groups of exponent dividing `N` has a largest member.

The two consequences used downstream are exactly:

1. `R(m,N)` is a **finite** group;
2. every finite `m`-generated group of exponent dividing `N` is a quotient of
   `R(m,N)`, so a homomorphism `F_m -> H` onto such a group kills
   `ker(F_m -> R(m,N))`, hence kills every relator `s_j` of `(RB1)`.

Clause 2 is immediate from the definition of `R(m,N)` as the largest
residually finite quotient of `B(m,N)`: a finite `m`-generated exponent-`N`
group is a finite quotient of `B(m,N)`, hence a quotient of its largest
finite quotient.
