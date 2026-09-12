---
rg: 2
id: full-q-quarter-half-cross-double-coset-proof
kind: route
title: Separate the source algebra from the adjacent-Whitehead double coset
target: full-q-quarter-half-cross-is-not-packet-universal
requires:
  - b2-b3-pair-full-hecke-four-native-sectors
  - full-moving-hecke-packet-retains-q-kernel-profile
---

Work in the exact binary matrix restriction to the eight projective
summands used by `full-moving-hecke-packet-retains-q-kernel-profile`.  All
named packet words preserve this finite direct summand, so their images
generate a finite group `G`.

Put

```text
K=<L_0,r,l>,                 r=x_58(a_2),
l=x_69(a_3),                 g=J_1J_2.                 (1)
```

The arrow list for `L_0` in this chart is

```text
q5->q6, q4->q5, q2->q4, q2->u2, q4->u3,
q2->u3, u1->u3, u1->q5, u1->q6, u2->q6.              (2)
```

The two extra roots add only

```text
r: u2->q5,                    l: u3->q6.               (3)
```

The directed graph `(2)--(3)` is acyclic: for example one may order the
vertices compatibly with

```text
{q2,u1} < {q4,u2} < {u3,q5} < q6.                    (4)
```

After choosing any total refinement of `(4)`, every generator of `K` is
strictly unitriangular.  Hence `K` lies in a finite unitriangular group over
`F_2` and is a `2`-group.

On the five middle projective summands the two native Whiteheads are the
literal adjacent swaps

```text
J_1=(u1 u2),                    J_2=(u2 u3).            (5)
```

Consequently `g=J_1J_2` is a nontrivial three-cycle.  Its image in `G` has
order three, so

```text
g notin K.                                                (6)
```

Now pass to the complex group algebra.  Since

```text
Q=e_(L_0,lambda_0),
F=Q(1+r)(1+l)/4,                                      (7)
```

one has `F in C[K]`.  The four-sector theorem proves in every exact packet
representation that `F` has one quarter of the nonzero `Q` rank; in
particular `F!=0` in the faithful left regular representation of `G`.

Expanding `(7)` in the group basis gives the support containments

```text
supp(F) subset K,               supp(FgF) subset KgK. (8)
```

For any subgroup and any element outside it, the double cosets `K` and
`KgK` are disjoint: an equality `k_0=k_1 g k_2` would imply
`g=k_1^(-1)k_0k_2^(-1) in K`.  Thus `(6)` gives

```text
K intersect KgK = empty.                               (9)
```

The group elements form a linearly independent basis of `C[G]`.  By
`(8)--(9)`, `FgF` and every nonzero scalar multiple of `F` have disjoint
group-basis support and cannot be equal.  The left regular representation
of `G` is faithful on `C[G]`, so in that exact finite-dimensional packet
representation

```text
FJ_1J_2F != (1/2)F.                                  (10)
```

This is compatible with the two adjacent-character computations: those
are nonfaithful monomial quotients in which different group-algebra support
can act by the same compressed operator.  The argument does not compute
the norm or trace mass of the Hecke operator `FgF`, so it leaves the
positive-cross-Gram frontier unchanged.
