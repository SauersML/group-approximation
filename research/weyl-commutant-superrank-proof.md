---
rg: 2
id: weyl-commutant-superrank-proof
kind: route
title: Average conjugation and compute its matrix-space trace by characters
target: weyl-commutant-superrank-detects-rectangular-return
requires: []
---

Finite-group averaging makes `(WCS1)` the orthogonal projection onto the
fixed vectors of the conjugation representation, namely the commutant.
On `M_d ~= C^d tensor conjugate(C^d)`, conjugation by `rho(q)` is
`rho(q) tensor conjugate(rho(q))`, whose ordinary trace is
`|Tr(rho(q))|^2`.  Divide the trace of `(WCS1)` by `d^2` to get `(WCS2)`.

On a nontrivial central phase of `H_N(p)`, finite Stone--von Neumann gives

```text
rho ~= pi_zeta tensor 1_m,       dim(pi_zeta)=p^N.
```

Its commutant is `1_(p^N) tensor M_m`, of dimension `m^2`, while the Hilbert
dimension is `p^N m`.  Their squared ratio is `p^(-2N)`, proving `(WCS3)`
and `(WCS4)`.

Finally, if two packet actions are conjugate together with the same
multiplicity reservoir, conjugation by that unitary carries one commutant
onto the other.  Their averaging projections are unitarily conjugate on
matrix Hilbert space and have equal normalized supertrace.  The unequal
values in `(WCS4)` therefore give the claimed floor.
