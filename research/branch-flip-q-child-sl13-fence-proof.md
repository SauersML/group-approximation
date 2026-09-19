---
rg: 2
id: branch-flip-q-child-sl13-fence-proof
kind: route
title: Conjugate the q-child triangle by the branch flip and close the thirteen atom carrier
target: branch-flip-weyl-joins-complementary-q-child-to-native-head
requires:
  - one-arm-return-of-complementary-q-child-stays-orthogonal
  - binary-branch-flip-weyl-has-s3-c2-model
  - projective-star-profile-has-zero-hecke-source
---

The binary inverse and cross-zero relations give

```text
w^2=1,             wqw=p,             wa_1=p,
b_1w=p.                                               (1)
```

In the elementary image the Weyl word `(BFQ3)` is the two-by-two block
matrix

```text
[[0,w],[w,0]]
```

on coordinates `7,10`.  The standard non-opposite Weyl conjugation rows
immediately send `U` and `V` to the last two roots in `(BFQ4)`.  To derive
the first equality inside the Steinberg group without appealing to an
opposite-root matrix identity, choose a spare index `k` and write

```text
Q=[x_(7,k)(q),x_(k,10)(1)].                            (2)
```

Conjugation by `Omega` sends the two factors in `(2)` to
`x_(10,k)(wq)=x_(10,k)(b_1)` and `x_(k,7)(w)`.  Their ordinary composable
root commutator is `x_(10,7)(b_1w)=x_(10,7)(p)`.  Thus all three equations
in `(BFQ4)` are ordinary Steinberg equalities.  In particular the first is
not an abstract equality of supports: it identifies the same group-word
occurrence `Q` with the native root `x_(10,7)(p)` through the displayed
Weyl word.

For the finite closure, the thirteen labelled coordinate summands in
`H union C` are pairwise orthogonal.  Prefix cancellation supplies all
matrix units used by the old native and complementary heads.  The block
form of `Omega` sends

```text
q@10 -> p@7,        p@7 -> q@10,
q@7  -> p@10,       p@10 -> q@7,
```

and fixes the other nine atoms.  This proves `(BFQ5)` and realizes every
displayed generator inside `SL_13(F_2)`.

It remains to prove that the generated group is all of `SL_13`.  Put
`H'=Omega(H)`.  The sets `H,H'` overlap in eight atoms.  Whenever two
matrix-unit sets `X,Y` overlap in an atom `r`, the Steinberg commutator

```text
[x_(i,r)(1),x_(r,j)(1)]=x_(i,j)(1)                    (3)
```

supplies every cross root from `X-Y` to `Y-X`, and the reversed choice
supplies the opposite roots.  Hence `SL(H)` and `SL(H')` generate
`SL(H union H')`, which here is the twelve-atom group obtained by adjoining
`q@7,q@10` to `H`.  Its intersection with `C` contains those two atoms, so
one more application of `(3)` with the old complementary `SL(C)` adjoins
`p@2` and proves `(BFQ6)`.

Finally use the natural action of `SL_13(F_2)` on its nonzero vectors.  A
transvection has `2^12-1` nonzero fixed vectors and hence `2^11=2048`
two-cycles, giving the first rank in `(BFQ7)`.  For the three commuting star
roots, the negative character requires the three target bits to be one;
the remaining ten bits are free and each compatible orbit has size two.
This gives `2^9=512` copies and the second rank.

For `F_Hecke`, apply the native negative-stabilizer certificate vector by
vector.  If one of the first three chain bits is zero, the corresponding
negative simple root fixes the vector.  If all three are one, the product
of the positive derived root with the middle negative simple root fixes it
and has negative character.  This argument ignores all other native and
complementary bits, so every stabilizer in the thirteen-bit action contains
a character-negative element.  The signed average is therefore zero,
which proves the last rank in `(BFQ7)` and completes the finite fence.
