---
rg: 2
id: full-q-native-quarter-range-counterprofile-proof
kind: route
title: Evaluate the two literal Whitehead images of the rank-one quarter source
target: full-q-native-quarter-source-has-distinct-literal-ranges
requires:
  - b2-b3-pair-full-hecke-four-native-sectors
  - full-moving-hecke-packet-retains-q-kernel-profile
---

Use the bit order

```text
(u_0,u_1,u_2,u_3,u_4)=(q@5,e_1@7,e_2@8,e_3@9,e_3@2). (1)
```

The proof of `full-moving-hecke-packet-retains-q-kernel-profile` gives an
orthogonal basis of `Q` in its `Omega_0` constituent.  The four basis
vectors are the equal-sign sums on

```text
{17,19}x{17},  {17,19}x{25},
{21,23}x{17},  {21,23}x{25}.                          (2)
```

The root `l=x_69(a_3)` is the adjacent radical character reading vector
bit `u_3`.  Its positive cut keeps precisely the two components of `(2)`
whose vector coordinate is `17`; the coordinate `25` has `u_3=1`.

The root `r=x_58(a_2)` is the Levi transvection from `u_2` to `u_0`.
On a row character it toggles row bit `u_2` when row bit `u_0` is one.
Consequently it exchanges the two surviving components

```text
{17,19}x{17}  <-->  {21,23}x{17}.                    (3)
```

Their positive sum is the vector `f` in `(FQR5)`.  This proves directly in
the exact model that `rank(F)=1`.

On the five Levi coordinates the native words are the literal swaps

```text
J_1=(u_1 u_2),                  J_2=(u_2 u_3).         (4)
```

Applying `(4)` simultaneously to the row and vector coordinates fixes the
vector coordinate `17`.  The first swap permutes `19` with `21` and fixes
`17,23`, so it fixes their equal sum.  The second swap sends

```text
17 |-> 17,       19 |-> 19,       21 |-> 25,
23 |-> 27,                                             (5)
```

which proves `(FQR6)`.

Two nonzero rank-one projections have nonzero meet exactly when their
spanning vectors are collinear.  The supports in `(FQR5)--(FQR6)` differ,
so the vectors are not collinear and `R_1 meet R_2=0`.  Exactly two of the
four orthonormal basis coordinates agree, while both vectors have squared
norm four.  Their normalized inner product is therefore `2/4=1/2`, proving
`(FQR7)`.

The representation used here is the exact adjacent-character monomial
representation of the whole four-block parabolic quotient.  Hence the
actions of `B_2,B_3,r,l,J_1,J_2`, the signed source `L_0`, and the two flip
relations of `b2-b3-pair-full-hecke-four-native-sectors` all coexist in one
finite representation.  No relation is being checked only after an
unrelated specialization.

`experiments/full_q_native_quarter_range_audit.py` repeats `(2)--(5)`,
checks the rank-one source and the two literal images, and prints the
normalized cross coefficient.  It is intended to run through MSI only.
