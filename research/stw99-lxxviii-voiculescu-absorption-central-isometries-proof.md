---
rg: 2
id: stw99-lxxviii-voiculescu-absorption-central-isometries-proof
kind: route
title: Turn approximate absorption of two copies into central Cuntz isometries
target: stw99-lxxviii-essential-representation-central-o2
requires: []
---

Voiculescu's noncommutative Weyl--von Neumann theorem is the literature input:
a faithful essential representation of a separable unital C\*-algebra absorbs
its direct sum with itself.  Thus there are unitaries

```text
U_n : H -> H directSum H
```

such that, for every `a in A`,

```text
||U_n pi(a) U_n*-(pi(a) directSum pi(a))|| -> 0.
```

Let `j_1,j_2:H->H directSum H` be the coordinate isometries and set

```text
s_(i,n)=U_n* j_i.
```

For every `n`, these satisfy

```text
s_(i,n)* s_(j,n)=delta_(ij)1,
s_(1,n)s_(1,n)*+s_(2,n)s_(2,n)*=1.
```

The displayed approximate intertwining says
`||[s_(i,n),pi(a)]||->0` for every `a`.  Hence the classes `s_1,s_2` in
`B(H)_infinity cap pi(A)'` are Cuntz isometries and define a unital embedding
`O_2` into that relative commutant.  A fixed unital embedding
`O_infinity->O_2` gives the asserted copy of `O_infinity`.

Finally, if `A` is simple and infinite-dimensional and `pi` is faithful, then
`pi(A) cap K(H)` is an ideal of `pi(A)`.  If it were nonzero, simplicity would
put `1_H` in `K(H)`, forcing `H` finite-dimensional and contradicting faithful
representation of infinite-dimensional `A`.  Thus every such irreducible
representation is essential.
