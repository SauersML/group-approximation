---
rg: 2
id: commuting-double-commutator-overlap-proof
kind: route
title: Equalize the four telescoping overlaps by output commutation
target: commuting-double-commutator-has-direct-mark-overlap
requires:
  - involution-normal-product-forces-one-factor-overlap
---

With the convention `[x,y]=xyx^(-1)y^(-1)`, involutivity gives the exact
four-factor expansion

```text
[[A,z],B]
 = (A z A) z (B z B) (B A z A B).                    (DCP1)
```

These are four conjugates of `z`, with conjugators `A,1,B,BA`.  Since `Q` is
a spectral projection of `r` and `r` commutes with `A` and `B`, the projection
`Q` commutes with all four conjugators.  Traciality therefore makes the four
carrier overlaps identical:

```text
tau(Q A P A)=tau(QP),
tau(Q B P B)=tau(QP),
tau(Q B A P A B)=tau(QP).                              (DCP2)
```

Apply `involution-normal-product-forces-one-factor-overlap` with `k=4` to
`(DCP1)`.  Its summed form says that the sum of the four quantities in
`(DCP2)`, including `tau(QP)` itself, is at least `tau(Q)/4`.  They are equal,
so `4tau(QP)>=tau(Q)/4`, proving `(DCO2)`.

For the robust statement, the telescoping lemma loses `o(1)` from the
double-commutator discrepancy.  Moving `Q` past `A`, `B`, and `BA` changes
the three corresponding traces by at most the normalized-Hilbert--Schmidt
commutator errors (twice in total for `BA`).  Hence all four overlaps equal
`tau(QP)+o(1)`, and the same division by four proves `(DCO3)`.
