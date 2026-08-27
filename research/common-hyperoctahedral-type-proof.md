---
rg: 2
id: common-hyperoctahedral-type-proof
kind: route
title: Repeat every allowed assignment and use the tautological signed-permutation block
target: all-bcs-contexts-share-one-hyperoctahedral-signed-type
requires: []
---

The diagonal subgroup `A=(C_2)^D` acts on the coordinate lines of `C^D` by
the `D` distinct characters `chi_i`.  An `A`-invariant subspace is therefore
a sum of coordinate lines.  If it is also invariant under `S_D`, transitivity
forces that set of lines to be empty or all of `[D]`.  This proves that the
tautological representation of `K_D=A semidirect S_D` is irreducible.

Equation `(HST2)` is possible because `|R_c|` divides `D`.  On the coordinate
line indexed by `(a,j)`, every `d_(c,x)` acts by `a_x`.  Thus the nonzero
joint eigenspaces are precisely those indexed by `a in R_c`, each repeated
`D/|R_c|` times.

The restriction of `rho_D` to `A` is the multiplicity-free sum of the
coordinate characters.  In the simple block selected by `q_D`, multiplication
by `e_(chi_i)` is consequently the rank-one coordinate projection.  Since
`q_D` annihilates every other simple block, the identities

```text
e_i e_j=delta_(ij)e_i,           sum_i e_i=q_D
```

hold in `C[K_D]`, not merely after applying `rho_D`.  The canonical trace and
scalar-character statements follow from the standard primitive central
idempotent formula and `dim(rho_D)=D>1`.
