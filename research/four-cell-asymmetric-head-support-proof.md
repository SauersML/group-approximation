---
rg: 2
id: four-cell-asymmetric-head-support-proof
kind: route
title: Transport the four marked centers through the three asymmetric heads
target: four-cell-marked-star-has-an-eighth-head-flag
requires:
  - seventeen-root-star-has-marked-triple-overlap
  - marked-star-asymmetric-heads-have-half-quarter-sources
---

Use the four prescribed indices `4,5,6,11` in the four-`Q` inequality of
`(SRS2)`.  This proves `(FCS2)`.  Prefix cancellation gives
`a_4b_4=q`, so `(A_4,B_4)` has center `C_4`.  Its indices are disjoint from
the first three cells, proving the four-pair Pauli decomposition and the
equal rank of all atoms in the three commuting signs `Z_2,Z_3,Z_4`.

All calculations below take place in the abelian involution packet generated
by `C_1,C_2,C_3,C_4,Z_2,Z_3,Z_4`.  The only needed conjugations are

```text
Ad(H_i)(C_i)=Z_(i+1)C_i,
Ad(H_i)(Z_i)=Z_(i+1)C_iZ_i                 (i=2,3),    (1)

Ad(H_i^(-1))(C_i)=Z_(i+1)C_i,
Ad(H_i^(-1))(Z_i)=C_iZ_i                   (i=2,3),    (2)
```

and every displayed generator not forced by `(1)--(2)` is fixed.  For
example, `[x_(10,6)(b_4),C_3]=Z_4` because `b_4q=b_4`, while
`[A_3,Z_3]=C_3` because `a_3b_3=q`.  These are ordinary nonopposite
Steinberg commutators; all factors on the right commute.

For the first palindrome, `(1)` gives

```text
Ad(H_1H_2H_1)(C_1)=Z_3C_2C_1,
Ad(H_1H_2H_1)(C_2)=Z_3C_2.                            (3)
```

On the all-negative center carrier, the first equality requires `Z_3=-1`
and the second requires `Z_3=+1`.  The range intersection is zero, proving
`(FCS4)`.  The inverse calculation also sends `C_1` to `C_2C_1`, which is
`+1` on `E_4`, so its source intersection is zero as well.

For the second palindrome, direct substitution in `(1)--(2)` gives

```text
Ad(H_2H_1H_2)(C_1)=Z_3C_2Z_2C_1,
Ad(H_2H_1H_2)(C_2)=C_2,

Ad((H_2H_1H_2)^(-1))(C_1)=C_2Z_2C_1,
Ad((H_2H_1H_2)^(-1))(C_2)=C_2.                       (4)
```

Thus the range condition is `Z_2Z_3=-1` and the source condition is
`Z_2=-1`, proving `(FCS5)`.

For the nested-corner check, `E_4 meet H_2E_4H_2^(-1)` forces `Z_3=+1`.
Conjugating the additional sign gives

```text
Ad(H_2)(Z_2)=Z_3C_2Z_2.
```

On the all-negative center carrier, the two copies of `Z_2=+1` therefore
have zero intersection.  Keeping opposite `Z_2` signs instead gives the
two quarter atoms; this is why the next nonzero refinement must use the
monotone transported corner rather than the same-corner compression.

For the monotone word, repeated use of `(1)` gives

```text
Ad(H_3H_2H_1)(C_1)=Z_4C_3Z_3C_2Z_2C_1,
Ad(H_3H_2H_1)(C_2)=Z_4C_3Z_3C_2,
Ad(H_3H_2H_1)(C_3)=Z_4C_3.                           (5)
```

Because all four centers are `-1` on `E_4`, equations `(5)` successively
force

```text
Z_4=+1,                  Z_3=-1,                  Z_2=-1. (6)
```

In the inverse direction, `(2)` gives the three independent conditions

```text
Z_2=+1,                  Z_3=+1,                  Z_4=+1. (7)
```

The conjugated center projections commute with `E_4`; hence the products
`T_321T_321^*` and `T_321^*T_321` are exactly the intersection projections
in `(6)--(7)`.  Pauli balance proves their relative rank `1/8` and `(FCS6)`.

The same coefficient calculation used for the first two corrected
Whiteheads defines `J_3` and shows that `U_3=w_(6,11)(1)J_3` swaps cells
three and four.  The three label swaps and the three outer Weyls separately
satisfy the type-`A_3` Coxeter relations, so the reservoir factors do also.
In `S_4`, a product containing each adjacent transposition once is a
four-cycle.  Any length-three head word exposing all of `Z_2,Z_3,Z_4` must
contain `H_1,H_2,H_3` once each; omission of `H_i` leaves the corresponding
new sign absent from the transported-center equations.  This proves the
shortest-word fence.

Finally apply `(1)--(2)` to `H_3H_2H_1H_2H_3`.  Its range equations reduce
to `Z_2Z_3Z_4=+1`, and its source equations reduce to `Z_2=-1`.  Both are
single Pauli equations and hence have relative rank `1/2`.  Its optimistic
reservoir word `V_3V_2V_1V_2V_3` is a conjugate of `V_1` and therefore an
involution, proving the stated tradeoff between involutive holonomy and
retention of the eighth flag.
