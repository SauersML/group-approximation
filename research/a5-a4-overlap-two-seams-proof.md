---
rg: 2
id: a5-a4-overlap-two-seams-proof
kind: route
title: Compute the restriction kernel and exhibit nonextendable adjacent charts
target: a5-a4-overlap-has-two-seam-charges
requires: []
---

Write the irreducibles of `A4` as `1,1',1'',3`.  Restriction of the five
irreducibles of `A5` is

```text
Res(1)=1,
Res(3)=Res(3')=3,
Res(4)=1+3,
Res(5)=1'+1''+3.                                      (ASP1)
```

These identities follow immediately by restricting the ordinary character
table of `A5` to the identity, the double transpositions, and the two classes
of three-cycles in `A4`.  The three image vectors

```text
1,                 3,                 1'+1''+3
```

are independent, while `Res(4)=Res(1)+Res(3)`.  Hence restriction has rank
three and its kernel has rank two.  The two displayed elements in `(ASC1)`
are independent and lie in the kernel, so they form a basis.

Now take two abstract copies `G_0,G_1 ~= A5` and identify standard subgroups
`H_i ~= A4`.  Since both three-dimensional irreducibles restrict to the
unique three-dimensional irreducible of `A4`, choose a unitary intertwiner
and conjugate the second action so that

```text
3|_(H_0) = 3'|_(H_1)
```

as literal operators on `C^3`.  The universal property gives a unitary
representation of `G_0 *_(A4) G_1`.  Similarly, `(ASP1)` aligns `4` on one
copy with `1+3` on the other on `C^4`.

Realize `G_0,G_1` as two adjacent point stabilizers in `A6`.  They intersect
in `A4` and generate `A6`, so there is a natural surjection

```text
G_0 *_(A4) G_1 -> A6.                                 (ASP2)
```

The complex irreducible degrees of `A6` are

```text
1,5,5,8,8,9,10.
```

Thus every representation of `A6` in dimension three or four is trivial.
The two amalgam representations above are nontrivial on each `A5` copy, so
neither factors through `(ASP2)`.  This proves both the two-dimensional seam
kernel and the exact nonextension assertion.

