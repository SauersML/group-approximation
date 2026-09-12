---
rg: 2
id: dihedral-common-partial-swap-proof
kind: route
title: Extract and estimate the shared partial isometry from the dihedral spin sector
target: dihedral-spin-packet-supplies-common-partial-swap
requires: []
---

Represent

```text
D_8=<z,j,y | z^2=j^2=y^2=1, y central, zj=yjz>.
```

Split by the `z` eigenspaces and write
`J=[[a,S],[S^*,d]]`.  On `P_spin=(I-Y)/2`, the relation says `ZJ=-JZ`, so
`J` exchanges the two `Z` halves unitarily.  On the complement `Z,J`
commute.  Hence

```text
SS^*=P_spin|_(H_+),   S^*S=P_spin|_(H_-).
```

For any block diagonal involution `D=diag(A,B)`, the off-diagonal blocks of
the additive commutator `[D,J]` are `AS-SB` and its adjoint.  Therefore

```text
2 Tr((AS-SB)^*(AS-SB))/dim(H)<=||[D,J]||_2^2.
```

Padding the smaller half changes normalization by at most two, yielding a
dimension-free bound of each Gram row by the ordinary word relator
`djdj=1`.  The same `j`, hence the same `S`, occurs in every row.

If the spin halves have dimension `r`, then

```text
||S||_2^2>=tau(P_spin)/2=||Y-I||_2^2/8,
```

so separation of the central mark forces positive common source mass.
Conversely, from any exact nonzero Gram operator `G=S|G|`, its polar partial
isometry obeys all intertwining and predicate rows on the support of `|G|`.
The standard Julia reflection built from this `S`, together with
`Z=diag(I,-I)`, realizes the dihedral presentation and keeps `y` nontrivial.
Thus completeness and the claimed robust common-swap estimate both hold.
