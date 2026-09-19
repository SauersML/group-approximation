---
rg: 2
id: payload-range-sum-three-character-model-proof
kind: route
title: Put the three range signs on one two-bit character orbit
target: payload-range-sum-whitehead-has-three-character-model
requires:
  - atomic-leavitt-gap-on-nonzero-matrix-corner
  - leavitt-range-sum-fold-is-first-object-erasing-row
  - outer-root-leavitt-table
---

First verify that the displayed prototype is an honest fixed Leavitt
occurrence table.  The two diagonal and crossed-zero commutators are the
four `t_i s_j` paths of `outer-root-leavitt-table`.  For each `i`, the
standard three-elementary Whitehead block for the partial inverse pair
`t_i s_i=A`, `s_i t_i=e_i` conjugates the active diagonal corner to the
`e_i` corner by direct block multiplication.  Conjugating the two input
roots with that same word therefore conjugates their output commutator `J`
to `C_i`.  Fixed spare-index permutations return both `C_i` to one common
root coordinate.  In that coordinate the final equation `C_0C_1=J` is
exactly the fold `(LRF3)--(LRF4)` from
`leavitt-range-sum-fold-is-first-object-erasing-row`.  Hence every row in
`(PCR1)--(PCR2)` is a fixed null word before considering the model below.

Let `E_0,E_1,E_2` be the standard basis projections of `C^3` and put

```text
J  =diag( 1,-1,-1),
C_0=diag(-1,-1, 1),
C_1=diag(-1, 1,-1).                                   (1)
```

The three signs commute, are involutions, have equal negative rank two, and
satisfy

```text
C_0C_1=J.                                              (2)
```

Let `W_0` be the permutation swapping `E_0,E_2`, and let `W_1` swap
`E_0,E_1`.  Then

```text
W_iJW_i^(-1)=C_i.                                      (3)
```

Work on

```text
H=C^3 tensor C^2 tensor C^2
```

and write `P=(1-J)/2`, extended trivially over the last two factors.  With
`sigma_x,sigma_z` the Pauli matrices, define controlled Pauli involutions

```text
X_0=(1-P)+P(I tensor sigma_x tensor I),
Z_0=(1-P)+P(I tensor sigma_z tensor I),
X_1=(1-P)+P(I tensor I tensor sigma_x),
Z_1=(1-P)+P(I tensor I tensor sigma_z).                (4)
```

On `(1-P)H` all four operators are the identity.  On `PH`, each same-index
pair anticommutes and the two tensor-factor pairs commute.  Therefore

```text
[X_i,Z_i]=(1-P)-P=J,
[X_i,Z_j]=1                         (i!=j).             (5)
```

Extend each `W_i` trivially over the Pauli factors and set

```text
X_i'=W_iX_iW_i^(-1),             Z_i'=W_iZ_iW_i^(-1).
```

Conjugating `(5)` and using `(3)` gives

```text
[X_i',Z_i']=C_i.                                       (6)
```

Equations `(2)`, `(5)`, and `(6)` prove the complete prototype table.
Moreover `P` has rank eight, so the prescribed nontrivial spectral atom of
`J` survives.

If `(PCR1)--(PCR2)` implied `(BAC1)`, every prototype discrepancy would be
zero in this exact model and the right side of `(BAC1)` would vanish.  It
would then produce an exact binary Leavitt family in `PM_12(C)P`, contrary
to `atomic-leavitt-gap-on-nonzero-matrix-corner`.  Hence the prototype does
not imply the three-row compiler.

The escape is visible directly in `(1)--(3)`: `W_iP W_i^*` is the negative
projection of `C_i`, not a subprojection of `P`.  Its intersection with `P`
has rank one on the `C^3` factor and its other rank-one part lies in
`(1-P)C^3`.  The output equations therefore authenticate the coefficient
products while failing exactly the required same-atom return.
