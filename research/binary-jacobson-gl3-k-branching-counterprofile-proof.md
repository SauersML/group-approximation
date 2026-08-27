---
rg: 2
id: binary-jacobson-gl3-k-branching-counterprofile-proof
kind: route
title: Restrict the PSL-two-seven character table and sum the regular multiplicities
target: binary-jacobson-gl3-k-branching-has-regular-counterprofile
requires: []
---

The identity, involution and order-three character values of the six complex
irreducibles of `G=GL_3(F_2)` are

```text
alpha       1A       2A       3A
--------------------------------
1            1        1        1
3            3       -1        0
3bar         3       -1        0
6            6        2        0
7            7       -1        1
8            8        0       -1.                       (JBRP1)
```

The subgroup `K~=S_3` meets these three classes in its identity,
transpositions and three-cycles.  If `chi` is a `G` character, inner products
with the three `S_3` characters give

```text
m_1       =(chi(1)+3 chi(2)+2 chi(3))/6,
m_epsilon =(chi(1)-3 chi(2)+2 chi(3))/6,
m_tau     =(chi(1)-chi(3))/3.                            (JBRP2)
```

Substitution of `(JBRP1)` in `(JBRP2)` gives every restriction in `(JBR2)`.
Since `w` is a transposition in `K`, it acts positively on `1`, negatively
on `epsilon`, and with one positive and one negative eigenvalue on `tau`.
This proves the `r_alpha` column.  Equivalently,

```text
r_alpha=(d_alpha-chi_alpha(2A))/2.                       (JBRP3)
```

As a check on the table, weight the restrictions by the degrees `d_alpha`.
The three resulting `K` multiplicities are

```text
sum_alpha d_alpha m_1(alpha)=28,
sum_alpha d_alpha m_epsilon(alpha)=28,
sum_alpha d_alpha m_tau(alpha)=56.                       (JBRP4)
```

Thus `lambda_G|_K=28 lambda_K`, as required by the index
`[G:K]=168/6=28`.

An irreducible `alpha box beta` of `F=G_Q x G_P` occurs in `lambda_F` with
multiplicity `d_alpha d_beta`.  After restriction to `K` it contributes

```text
d_alpha m_sigma(alpha) d_beta^2                          (JBRP5)
```

copies of a `K`-type `sigma`.  Summing `(JBRP5)` over `beta` multiplies
`(JBRP4)` by

```text
sum_beta d_beta^2=|G|=168,
```

which proves `(JBR4)--(JBR5)`.  Finally `(JBRP3)` gives

```text
sum_alpha d_alpha r_alpha
 =3*2+3*2+6*2+7*4+8*4=84,                               (JBRP6)
```

and `(JBR6)` follows.

Every relation in the two shortest cells is an equality of unitary words.
If one forgets the actual matrix blocks and retains only source/target ranks
inside the `K` reservoirs, those words preserve total rank.  The positive
integral vector `(JBR3)` satisfies all restriction and conservation rows, so
no homogeneous linear combination of those rows can force one of its marked
coordinates to vanish.  This proves the stated counterprofile and precisely
locates the missing nonlinear holonomy input.
