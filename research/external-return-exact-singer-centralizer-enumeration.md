---
rg: 2
id: external-return-exact-singer-centralizer-enumeration
kind: route
title: Enumerate the external quotient and audit every Singer centralizer
target: external-return-group-has-only-spectator-singer-centralizers
requires:
  - signed-hecke-normalizer-has-eight-external-root-returns
  - eight-external-returns-have-no-whitehead-gauge-lock
  - native-whitehead-hecke-head-has-order-seven-anchor
---

Represent a binary `7`-by-`7` matrix by its seven bit rows in coordinate
order `(2,4,5,6,7,8,9)`.  In the topological order

```text
(6,9,5,8,4,7,2),
```

the external list contains the six adjacent arrows.  Their iterated root
commutators give every forward transvection.  Thus the external roots alone
generate `UT_7(F_2)`, of order `2^21`, and contain the ten displayed
`L_0` generators.

For the independent coset audit, close the ten generators of `L_0` and
verify that the result contains `8192` matrices.  For each of the eight
external transvections, conjugate every `L_0` generator and check exact
membership in that closure.  Since each external transvection is an
involution, this proves equality under conjugation and hence normality of
`L_0` in `G_X`.

Enumerate `G_X/L_0` by breadth-first search on the eight external
generators.  Two representatives `r,s` define the same coset exactly when

```text
r^(-1)s in L_0.                                         (1)
```

The search closes after `256` right cosets.  Normality and the explicit `8192`
elements of `L_0` then give `(ESC2)` and express every element of `G_X`
uniquely as `r l` for one stored representative and `l in L_0`.

For each of those `256*8192` matrices and each literal head `(ESC3)`, test

```text
g t_i = t_i g.                                          (2)
```

Exactly `64` matrices pass `(2)` in each row.  Independently close the two
subgroups on the right of `(ESC4)`; both have order `32768`.  Exact set
difference finds zero centralizers outside the appropriate subgroup.  The
artifact also closes the three simple-root generators displayed in `(ESC5)`
and checks exact set equality with the corresponding centralizer.  Each is
the unitriangular group on the four coordinates complementary to the
Singer three-space and has order `2^6=64`.  This proves `(ESC4)--(ESC5)` and
the claimed all-word fence.

There is also a short structural verification of the last enumeration.
The active Singer spaces are

```text
A_1=<e_4,e_7,e_8>,               A_2=<e_5,e_8,e_9>,
```

and each head is the identity on its complementary four-space.  The active
minimal polynomial is `X^3+X+1`, coprime to `X+1`, so a commuting matrix
has no cross blocks.  The invertible active centralizer is `F_8^times`, of
order seven.  A unitriangular element has two-power order, so its active
block must be the identity.  The complementary unitriangular blocks are

```text
UT(6,9,5,2)=<x_96,x_59,x_25>,
UT(6,4,7,2)=<x_46,x_74,x_27>.
```

Finally `x_25=[x_24,x_45]` and `x_46=[x_45,x_56]` lie in `L_0`; the other
four displayed simple roots are precisely the fixed spectators.  This
proves `(ESC4)` without exhaustive matrix closure.
