---
rg: 2
id: atlas-q14-simple-overgroup-index-is-at-least-24
kind: claim
title: Every augmented finite-simple Atlas escape has A8 index at least twenty-four
distinct_from:
  atlas-q14-finite-quotient-is-simple-overgroup-test: that reduces an arbitrary finite escape to two marked A8 copies in a larger simple group; this supplies the first substantial order and intersection sieve on that simple group.
  atlas-a4-packet-biclique-decomposition: that identifies the two packet gadgets inside one chart; this describes the cross-chart A4 amalgams and then uses finite permutation-group theory.
  atlas-a4-19243-classical-collapse: that excludes the equal ambient group S=A8; this also excludes the next fifteen possible chart indices.
---

Let `S` be a finite simple group and let

```text
A=i_1(A8),  B=i_2(A8),  S=<A,B>                     (OSI1)
```

solve the twelve distinct packet relations, `q_19243`, and q14 as in the
finite-simple overgroup test.  Put

```text
n=[S:A]=[S:B].                                       (OSI2)
```

Then

```text
n >= 24,             |S| >= 24 |A8| = 483840.       (OSI3)
```

The forced local subgroup geometry is as follows.

1. Every packet edge, joining an order-two letter `b` in one chart to an
   order-three letter `a` in the other, generates an embedded `A4`:

   ```text
   <b,a> ~= A4.                                      (OSI4)
   ```

   The twelve edges therefore form four cross-chart `A4` rectangle amalgams
   on the `K_(2,2) disjointUnion K_(2,4)` incidence graph.  Edges in one row
   share their marked `C2`; edges in one column share their marked `C3`.
2. If `t_1=i_1(t23)` and `t_2=i_2(t23)`, q14 says

   ```text
   [t_1,t_2]=1.                                      (OSI5)
   ```

   Thus either `t_1=t_2` is a transvection in `A intersect B`, or
   `<t_1,t_2> ~= C2 x C2`.  In particular, if `t_1` is not in `B`, then

   ```text
   |C_S(t_2)| >= 2 |C_B(t_2)| = 384,                 (OSI6)
   ```

   and symmetrically with the charts exchanged.
3. For `T=A intersect B`,

   ```text
   [A8:T] <= n.                                      (OSI7)
   ```

   Also conjugation gives the general normalizer constraint

   ```text
   [N_S(A):A C_S(A)] <= |Out(A8)|=2.                 (OSI8)
   ```

At the first arithmetically possible index `n=24`, the residue is especially
small.  The intersection is one of

```text
A intersect B ~= A7                 (index 8),
A intersect B ~= 2^3:GL_3(2)        (index 15).       (OSI9)
```

Moreover the coset action of `S` has exactly one of two forms:

```text
primitive degree 24, with A-subdegrees 1,8,15;        (OSI10)

or

imprimitive with twelve blocks of size two,
S < A12 and [A12:S]=495.                              (OSI11)
```

This does not assert that either index-24 case exists.  It is the first residue
left by the low-index orbit sieve in this claim.  The stronger
`atlas-q14-simple-overgroup-index-is-at-least-32` eliminates both cases and
continues the sieve through index 31.  No finite list for arbitrary `n` follows
from local subgroup orders alone: the relations have an infinite universal
completion, so a further global classification or collision-specific fusion
argument is still required.
