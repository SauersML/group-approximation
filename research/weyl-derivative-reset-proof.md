---
rg: 2
id: weyl-derivative-reset-proof
kind: route
title: Multiply the two shifted commutator forms and use the transverse old selector
target: weyl-derivative-reset-preserves-schur-spin-scale
requires:
  - finite-schur-clifford-packet-flexible-hs-exactification
  - finite-group-shared-overlap-polar-alignment
---

In copy `a`, the defining cross commutator is

```text
[p_r^(a),q_s^(a)]
 =J^(C_rs+a(A_i)_rs) product_j z_j^((A_j)_rs).          (1)
```

Replacing `a` by `a+1` and `z_i` by `Jz_i` preserves `(1)`, so `(WDR2)` is
an automorphism.  Since distinct copies commute, the commutator of the two
orbit products is the product of their two commutators.  Every `z_j` occurs
twice, the constant `C_rs` occurs twice, and only `(A_i)_rs` remains.  This is
`(WDR4)`.  The same copy swap fixes each product in `(WDR3)`, proving
centralization by `s_i`.

Invertibility of `A_i` and
`clifford-commutator-rank-is-packet-dimension` give the unique `2^N`
dimensional marked spin type of `L_i`.  Each old selector sector of `A` has
the same spin dimension because `U(x)` is invertible.

Equation `(WDR6)` is just the semidirect-product relation, read in the other
direction.  On a `J=-1` representation it sends the spectral projection
`(1+s_i)/2` to `(1-s_i)/2`.  The conjugating operator commutes with `L_i` and
the other selector involutions, so it pairs the two fresh signs inside every
conditional spin isotypic carrier.  Finally, restriction to either `A` or
`L_i` decomposes that carrier into irreducibles of the same dimension `2^N`;
dimension gives `(WDR7)`.

The approximate conclusion is the fixed-finite-table argument cited in the
claim: exactify `R_i`, align its corrected overlap with the adjacent packet,
apply the exact multiplicity identity, and charge the discarded corner by
`C sqrt(E)`.

For a general direction `v`, replace `e_i` throughout by `v`. Translation by
`v` is still an involution, and multiplying `z_j` by `J^(v_j)` preserves the
shifted copy relations. The orbit-product commutator is
`U(x)+U(x+v)=A(v)`, so the identical proof applies.
