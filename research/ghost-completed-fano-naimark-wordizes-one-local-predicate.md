---
rg: 2
id: ghost-completed-fano-naimark-wordizes-one-local-predicate
kind: claim
title: The ghost-completed Fano Naimark column has an exact local dihedral wordizer
distinct_from:
  fano-cap-sequential-products-form-an-algebraic-naimark-carrier: that uses only the seven honest cap channels and obtains nonsharp cap-label effects; this adds the missing ghost channel and isolates precisely the forbidden atom.
  shared-multiplicity-commutator-builds-selected-hybrid-row: that handles an arbitrary truth table on one selected type; this gives an explicit eight-channel Fano dilation and identifies its common-source column.
---

**ESTABLISHED LOCALLY; NOT A COMMON-SOURCE PROMOTION.**  Work in the affine
eight-atom context with PVM `(P_t)_(t in F_2^3)`.  Put

```text
F=P_0,
E_lambda=sum_(t:lambda(t)=1)P_t
                 (lambda in F_2^3\{0}).               (GCN1)
```

Every nonzero `t` lies in four maximal caps and the ghost lies in none, so

```text
sum_(lambda!=0) E_lambda=4(1-F).                       (GCN2)
```

Consequently the eight-entry column

```text
V=(E_lambda/2)_(lambda!=0) direct-sum F               (GCN3)
```

satisfies `V^*V=1`.  If `L_g` is the external ghost-coordinate projection
and `Q=VV^*`, then

```text
V^*L_gV=F,                [L_g,Q]=0.                   (GCN4)
```

Thus the cap labels remain nonsharp POVM effects, but the completed ghost
label is a genuine reducing projection and recovers exactly the forbidden
atom.

There is an explicit finite-dimensional unitary completion.  Choose one
input coordinate `s` among the seven cap coordinates.  For every honest
`t`, let

```text
v_t=(1/2)sum_(lambda:lambda(t)=1)e_lambda              (GCN5)
```

and choose a self-adjoint orthogonal unitary `W_t` on the eight-coordinate
label space which sends `e_s` to `v_t` and fixes the ghost axis.  A
Householder reflection inside the seven-dimensional nonghost space does
this.  Let `W_0` swap `e_s` with the ghost basis vector and fix their
orthogonal complement.  Then

```text
W=sum_t P_t tensor W_t,
W=W^*=W^(-1),                 V=W(1 tensor e_s).       (GCN6)
```

Let `Z=1-2L_g` and form the ordinary dihedral commutator word

```text
C=ZWZW.                                                     (GCN7)
```

On every honest assignment block, `W_t` preserves the ghost axis and
commutes with `Z`, so `C=1`.  On the ghost block, `W_0` swaps the `+1` and
`-1` axes of `Z`, so `C=-1` on their two-dimensional span and is `1`
elsewhere.  With normalized label trace,

```text
||C-1||_2^2=tau(F).                                    (GCN8)
```

Hence one ordinary group word exactly measures the local ghost mass with a
dimension-independent constant.

## Fixed finite Morita host

The selector involutions, `W`, and `Z` give a finite-group representation.
The selector group is elementary abelian and commutes with `W,Z`; on each
selector character the two involutions `W,Z` satisfy

```text
W^2=Z^2=1,                 (ZW)^4=1.                  (GCN9)
```

Thus the representation factors through the fixed finite group
`A times D_8`.  Repeated irreducible summands can be hosted in a fixed
matrix amplification of `C[A times D_8]`, equivalently in a finite
Hecke/Morita block.  In that selected block `(GCN7)` is literally the
ordinary `D_8` commutator word, not an additive group-algebra test.

Imposing `C=1` deletes the ghost `D_8` type and preserves the honest types.
This is a complete local predicate wordizer, but it does **not** preserve the
full eight-atom packet.  For several contexts the selected honest types can
still occupy mutually orthogonal multiplicity reservoirs over the shared
variable subgroup.  The construction therefore lands exactly at the
selected-type/source-alignment seam in
`common-partial-isometry-swap-game-compiler`; the tight column does not prove
`(CPS9)` or its forbidden-weighted form `(CPS12)`.

In particular, the construction does not close
`edgeful-or3-coefficient-link-compiler`.  It shows that nonlinear local
wordization is available without sharp cap profiles.  What remains is the
matrix-only promotion of all these locally selected types to one common
cross-context source.
