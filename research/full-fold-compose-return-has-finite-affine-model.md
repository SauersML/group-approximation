---
rg: 2
id: full-fold-compose-return-has-finite-affine-model
kind: claim
title: The full two-branch fold-compose-return cell has a finite marked affine model
invalidates:
  - full-fold-compose-return-closes-code
artifacts:
  - research/full-fold-compose-return-affine-proof.md
distinct_from:
  full-completeness-opposite-menu-has-finite-gl5-fusion: that separates coefficient direct-finiteness from a three-copy occurrence fusion; this tests the additional two-step right-then-left composition through both branches and both crossed-zero rows.
  payload-range-sum-whitehead-has-three-character-model: that stops at the three-character output fold; this adds two intermediate arm labels and realizes the resulting table by four-bit affine transvections.
---

**ESTABLISHED EXACT COMPOSABLE-LOOP FIREWALL.**  Use commutator convention
`[g,h]=ghg^(-1)h^(-1)`.  Let

```text
V=<A,C,R_0,R_1>_(F_2),       C_0=C,       C_1=A+C.      (FAR1)
```

Define four involutions in `GL(V)` by

```text
S_0: A |-> A+R_0, C |-> C+R_0,
S_1: A |-> A+R_1, C |-> C,
T_0: R_0 |-> R_0+A, R_1 |-> R_1,
T_1: R_1 |-> R_1+A, R_0 |-> R_0,                       (FAR2)
```

with every undisplayed basis vector fixed.  In the finite affine group
`V semidirect GL(V)`, vectors are commuting involutions and direct
calculation gives

```text
C_0+C_1=A,
[C_i,S_j]=delta_(ij)R_j,       [A,S_j]=R_j,
[T_i,R_j]=delta_(ij)A.                                  (FAR3)
```

The same `S_j` occurs in the two range summands and in their folded parent;
the same `T_i` is then used on both intermediate arms.  Therefore `(FAR3)`
is exactly the two-step test

```text
t_i ((s_0t_0+s_1t_1)s_j)=t_is_j=delta_(ij)A,           (FAR4)
```

including the full second branch and both crossed-zero returns.  The parent
mark `A` remains nonzero.

The finite model can retain the noncommuting payload/opposite-root
authentication at the output labels.  Let `K` be the finite
`GL_5(F_2)` packet used in
`full-completeness-opposite-menu-has-finite-gl5-fusion`, let
`z=x_15(1)`, and put `Omega=V^*`.  In

```text
K^Omega semidirect GL(V),                               (FAR5)
```

define, for each `v in V`,

```text
D_v(chi)=z^(chi(v)).                                    (FAR6)
```

Then `D_vD_w=D_(v+w)`, and the contragredient permutation action sends the
entire `v`-supported copy of every finite payload/opposite-root occurrence
to the corresponding `gv`-supported copy.  Replacing the vectors in
`(FAR3)` by the signs `D_v` proves the same table inside the finite group
`(FAR5)`, while every supported length-three payload loop and opposite-root
Whitehead is still a literal coordinatewise matrix identity.  In
particular `D_A!=1`.

The left regular representation of `(FAR5)` has zero defect on every row
and

```text
||lambda(D_A)-1||_2=sqrt(2).                            (FAR7)
```

Thus the composable completeness loop has no normalized-HS or operator-norm
MF payment.  Its finite escape no longer uses the old three-character
quotient: it promotes the two intermediate arms to independent affine
coordinates.  What is still absent is a relation identifying those
occurrence coordinates with left and right multiplication on one decoded
matrix reservoir.  No Property `(T)`, Kazhdan input, stability theorem,
trace hypothesis, literature result, or local compilation is used.

## Attempts

- **Use the old three-character packet.**  It has no independent `R_0,R_1`
  coordinates, so the full crossed table is not represented by its three
  signs alone.  Enlarging to `(FAR1)` supplies exactly the two missing
  intermediate labels.
- **Argue that reusing `S_j,T_i` forces coefficient direct-finiteness.**
  The transvections `(FAR2)` reuse each actor literally and satisfy all four
  matching/crossed rows, but they are automorphisms of an occurrence-label
  packet, not multiplication by finite coefficient operators on one
  corner.

DERIVATION
full-fold-compose-return-affine-proof

