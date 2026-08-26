---
rg: 2
id: positive-signed-actor-two-scale-profile-proof
kind: route
title: Enumerate fixed-source endpoint incidences of all positive signed actors
target: positive-signed-actor-two-scale-profile-is-partial-and-gauged
requires:
  - exceptional-endpoint-detector-products-stay-at-depth-three
  - signed-hecke-detectors-are-uniformly-mark-saturated-but-untyped
---

Let `G` be the constant actor matrix of `g`.  Since `g` fixes coordinate
`3`, conjugating `Y_m=1+b_mE_(k_m,3)` gives

```text
gY_mg^(-1)
 = product_(s in actor) x_(s,3)(G_(s,k_m)b_m).         (1)
```

The factors commute, and multiplication by `Y_m^(-1)` removes the diagonal
factor.  Therefore the endpoint factor `x_(r,3)(b_m)` occurs in
`[g,Y_m]` exactly when `G_(r,k_m)=1`.  All other factors commute with
`A_(r,m)=x_(1,r)(a_m)`, so

```text
[A_(r,m),[g,Y_m]]=x_13(a_mb_m)=z                     (2)
```

exactly on the incidences defining `C_Y(g)`.

The reverse calculation starts with `X_m=1+a_mE_(1,k_m)`.  Right
multiplication by `G^(-1)` shows that `[g,X_m]` has endpoint factor
`x_(1,r)(a_m)` exactly when `(G^(-1))_(k_m,r)=1`.  Commuting with
`B_(r,m)=x_(r,3)(b_m)` gives `z`, proving the interpretation of `C_X(g)`.

Close the ten generators to all `8192` elements of `L_0`, retain the
positive character kernel, remove the identity, and partition by conjugacy.
This gives `511` classes.  Direct inspection of the three native columns and
the corresponding inverse rows gives `(PSA2)` and the `184/327` split.  The
same established internal-normal-closure test which produced the `31`
root-free classes gives profile counts `23` at `{3}` and `8` empty, with no
inverse-row incidence.

For `(PSA3)`, the only relevant off-diagonal entries are
`G_(2,8)=G_(4,9)=1`.  Equation `(1)` gives the first and third identities
of `(PSA4)`, and `(2)` gives the other two.  Finally, tensor the two
occurrence edges with arbitrary commuting involutions `D_2,D_3` on a
multiplicity factor.  Because `g_*` acts trivially on that factor,

```text
[g_*,Y_m tensor D_m]=[g_*,Y_m] tensor 1.              (3)
```

Thus the complete nested commutator table is blind to `D_2,D_3`.  This
proves both the concrete occurrence and its scoped independent-gauge fence.
