---
rg: 2
id: head-square-whitehead-loop-proof
kind: route
title: Square the asymmetric head and close the corrected prefix triangle
target: head-square-whitehead-loop-preserves-deep-star-flag
requires:
  - four-cell-marked-star-has-an-eighth-head-flag
  - marked-star-outer-corrected-whiteheads-are-quarter-swaps
  - native-whitehead-hecke-head-has-order-seven-anchor
---

All named root elements are involutions.  The commutator

```text
[B_(i+1),A_i]
 =x_(k_(i+1),k_i)(b_(i+1)a_i)=X_i
```

commutes with both factors, so

```text
H_i^2=(B_(i+1)A_i)^2=X_i.                             (1)
```

By definition `J_i=X_iY_iX_i`, and therefore

```text
X_iJ_i=Y_iX_i,             J_iX_i=X_iY_i.             (2)
```

Both products in `(2)` have order three in the literal characteristic-two
Whitehead block.  The outer Weyl `L_i` uses only the two outer indices and
commutes with `X_i,Y_i,J_i`.  Hence

```text
(H_i^2U_i)^3
 =(X_iL_iJ_i)^3=L_i^3(X_iJ_i)^3=L_i,
```

and the reversed identity is identical.  This proves `(HSW2)`.

The corrected Whitehead swaps the two anchored cells, so it swaps
`Z_i,Z_(i+1)`.  Conjugation by `X_i` fixes `Z_(i+1)` and sends

```text
Z_i |-> Z_iZ_(i+1),
```

by the composable root commutator.  Applying `U_i` first and then `X_i`
gives `(HSW3)`.  Both output signs are positive on the all-positive atom,
which proves zero leakage for every nested positive source flag containing
this adjacent pair.

In the Pauli tensor decomposition, `U_i=SWAP_(i,i+1) tensor V_i`.  The
label swap fixes pointwise the joint positive eigenspace of
`Z_i,Z_(i+1)` and acts trivially on all other label qubits.  Compressing to
that eigenspace proves `(HSW3')` with the same named reservoir involution
`V_i`, not a newly chosen chart gauge.

Finally `X_i` fixes `A_i`, while

```text
[A_(i+1),X_i]
 =x_(alpha_(i+1),k_i)(a_(i+1)b_(i+1)a_i)
 =x_(alpha_(i+1),k_i)(a_i)=F_i,                       (3)
```

because `a_(i+1)b_(i+1)=q` and `qa_i=a_i`.  Equation `(3)` proves
`(HSW4)`.  Its root position differs from every anchored `A` root, so the
fixed full-Pauli packet is not normalized even though its positive `Z`
atom is invariant.  Removing label charts from the three-stage identity
therefore yields the transition product `(HSW5)`, not the scalar equation
`D_(U_i)^3=1`.  This proves the stated chart-gauge fence.
