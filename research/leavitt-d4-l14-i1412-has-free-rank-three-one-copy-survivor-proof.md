---
rg: 2
id: leavitt-d4-l14-i1412-has-free-rank-three-one-copy-survivor-proof
kind: route
title: Exhibit the empty-Tietze cancellation scheme and reduce the inverse boundary
target: leavitt-d4-l14-i1412-has-free-rank-three-one-copy-survivor
requires:
  - leavitt-d4-l14-i1412-corrected-eq3-retraction-skeleton
---

Number the 29 positions of the corrected `COLORS,S` word from zero.  Take
the following same-color blocks:

```text
{0,16,28},
{1,3,5,7,15}, {2}, {4}, {6},
{8,10,12,14}, {9}, {11}, {13},
{17,19,21,23,27}, {18}, {20}, {22},
{24,26}, {25}.                                      (I14-1)
```

They are noncrossing.  The first block separates the intervals `1..15`
and `17..27`.  In each interval the displayed long block separates its
singleton gaps and the one nested long block.  There are 15 blocks, equal
to the certified minimum `minimum_blocks=15`, so `(I14-1)` is a maximal
scheme.

Multiplying the coefficient labels in each block and simplifying by
single-occurrence Tietze moves gives, with the corrected numbering
`1=g1,2=g2,3=g4,...,12=g13`,

```text
g1  = P,          g2  = Q,          g4  = Q^-1,
g5  = R,          g6  = 1,          g7  = R^-1,
g8  = 1,          g9  = Q^-1,       g10 = Q^-1,
g11 = Q^-1,       g12 = Q^-1,       g13 = P^-1.       (I14-2)
```

Here `P,Q,R` are unconstrained.  For completeness, the singleton blocks
first give `g6=g8=1`, `g4=g2^-1`, and the two copy-zero labels give
`g11=g4` and `g9=g11`.  The pair `{24,26}` gives `g10=g12`.
The block `{0,16,28}` then gives
`g12=g11=g10`, the nested copy-one block gives `g7=g5^-1`, and either
long copy-two block gives `g13=g1^-1`; its mate becomes the same relation.
Thus the quotient presentation has no relator in `P,Q,R`, agreeing with
the empty Tietze presentation in the corrected MSI output.

Write

```text
p=g1, u=g2, v=g4, w=g5, x=g6, y=g7, z=g8,
a=g9, b=g10, c=g11, d=g12, e=g13.
```

The raw corners used by the inverse carrier system are

```text
H  =d_1(ep)_2(uv)_1w_2x_1y_2z_1a_2b_3,
A0 =p_3(uv)_2w_3x_2y_3z_2a_3,
C1 =d_0(ep)_1u_0,
E2 =w_0,  E3=x_3,  E4=y_0,  E5=z_3.                  (I14-3)
```

Substitution of `(I14-2)` gives

```text
H=Q^-1_1 Q^-1_2 Q^-1_3,   A0=(P Q^-1)_3,   C1=1,
E2=R_0, E3=1, E4=R^-1_0, E5=1.                       (I14-4)
```

Finally the inverse boundary formula is

```text
K=A0^-1 H^-1 C1^-1 H E5^-1 H^-1 E4^-1 H
  E3^-1 H^-1 E2^-1 H.
```

The first `H^-1H` cancels.  After deleting `E5` and `E3`, the middle
`HH^-1` cancels and the adjacent copy-zero coefficients
`E4^-1 E2^-1=R_0R^-1_0` cancel.  Therefore

```text
K=A0^-1=(Q P^-1)_3.                                  (I14-5)
```

Since `P,Q,R` freely generate the coefficient quotient, `(I14-5)` is
nontrivial and is supported in precisely one coefficient copy.

