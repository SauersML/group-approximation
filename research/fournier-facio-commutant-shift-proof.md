---
rg: 2
id: fournier-facio-commutant-shift-proof
kind: route
title: Conjugate Gamma-commutants by the compression letter and read off the commuting simple copies
target: fournier-facio-regular-models-carry-commutant-shift
requires:
  - fournier-facio-group-contains-simple-wreath-shift
  - fournier-facio-nontrivial-quotients-contain-simple-wreath
---

Write `t=t_1`.  `theta=Ad(u(t)^*)` is a trace-preserving automorphism of
`M`.

**(CS1).**  Let `x in A` and `gamma in Gamma`.  Since `t gamma t^-1 in Gamma`,
`x` commutes with `u(t gamma t^-1)=u(t)u(gamma)u(t)^*`.  So
`theta(x)u(gamma)=u(t)^* x u(t gamma t^-1) u(t)=u(gamma)theta(x)`, and
`theta(A)<=A`.  For `j in J_0` we have `t j t^-1 in J_1<=Gamma`.  The same
computation with `u(j)=u(t)^* u(t j t^-1) u(t)` shows that `theta(x)`
commutes with `u(j)`.

**(CS2).**  `J_-k` centralizes `Gamma` for `k>=0` (clause (W3)), so
`u(J_-k)<=A`, and `theta(u(j))=u(t^-1 j t)` maps `u(J_-k)` onto
`u(J_-(k+1))`.

**(CS3).**  `u` is nontrivial, so it is injective on `J_0` by
`fournier-facio-nontrivial-quotients-contain-simple-wreath`.  `J_0` is
nonabelian, so some `u(j)`, `j in J_0`, fails to commute with `u(J_0)`.
That `u(j)` lies in `A` by (CS2) but not in `theta(A)`, by (CS1).

**(CS4).**  Induct.  `theta` is an automorphism of `M`, so it maps
intersections to intersections and the commutant of a set onto the commutant
of its image.  Then
`theta^n(A)<=theta(A cap u(J_0 ... J_-(n-2))')
 <=theta(A) cap u(J_-1 ... J_-(n-1))'
 <=A cap u(J_0 J_-1 ... J_-(n-1))'`.

**Regular character.**  If `tau(u(g))=0` for `g!=1`, the trace on the
subgroup `(+)_(k<=0) J_k` is its regular character.  So the generated von
Neumann algebra is `L((+)_(k<=0) S)`, the tensor product of the `L(J_k)`.
Each `L(J_k)` is a II_1 factor because an infinite simple group is ICC: a
finite conjugacy class gives a finite-index centralizer; the kernel of the
action on its cosets is then a finite-index normal subgroup, which is the
whole group, so the element is central and hence trivial.  The same
factorization of the trace on the internal direct product
`J_1 x ... x J_n x t^n Gamma t^-n<=Gamma` from (W7) gives the tensor
decomposition, with `Ad(u(t))^n(u(Gamma)'')=u(t^n Gamma t^-n)''`.
