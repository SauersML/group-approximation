---
rg: 2
id: two-matching-multiplicity-free-propagation-proof
kind: route
title: Fourier-expand overlap entries and close their support under the irreducible field generator
target: two-matchings-force-full-weyl-on-multiplicity-free-spectra
requires: []
---

Let

```text
H_(x,y)=<e_x,f_y>
```

be the unitary change-of-basis matrix.  Sandwich `(TM3)` between the U-basis
vectors `e_x,e_x'` and expand `W(b)` in its spectral characters.  Uniqueness
of Fourier coefficients on `V` gives

```text
H_(x,y) conjugate(H_(x',y))
 = H_(x,y+r_i) conjugate(H_(x',y+r_i)),
r_i=c_i+T_i^*(x+x').                                         (1)
```

Taking `x=x'` shows that every row support is invariant under

```text
C_0=span(c_0,c_1).                                             (2)
```

Repeat the same calculation with the roles of `U,W` exchanged and the
parameter `a=T_i b`.  Every column support is invariant under

```text
D_0=span(d_0,d_1),              d_i=T_i^(-*)c_i.                (3)
```

Choose one nonzero entry `H_(x,y)`.  Equations `(2)--(3)` imply that every
entry in

```text
(x+D_0) x (y+C_0)                                             (4)
```

is nonzero.  Because the atoms are one-dimensional, whenever two rows are
nonzero in one column their cross coefficient in `(1)` is nonzero.  Therefore
for every `d in D_0`, `(1)` adds `T_i^*d` to the translation invariance of the
row support.  The symmetric calculation adds `T_i^(-*)c` to the column
support for every newly obtained `c`.

Iterating gives subspaces

```text
C_(m+1)=C_m + sum_i T_i^* D_m,
D_(m+1)=D_m + sum_i T_i^(-*) C_m.                              (5)
```

and a nonzero full overlap rectangle

```text
(x+D_m) x (y+C_m)                                             (6)
```

at every stage.  At the stable value, `T_0=I` makes `C_infty=D_infty`, while
`T_1=A=A^*` makes this common nonzero subspace invariant under both `A` and
`A^(-1)`.  Irreducibility of the characteristic polynomial forces

```text
C_infty=D_infty=V.                                             (7)
```

Hence the chosen row and column have nonzero overlap with every character.
The multiplicity-free representations contain all `2^n` characters, proving
`(TM4)`.
