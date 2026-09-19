---
rg: 2
id: leavitt-degree-four-corner-nielsen-proof
kind: route
title: Protect the four long corners by excluded V4 and D8 endpoints
target: leavitt-degree-four-corner-subgroup-is-v4-d8-f4
requires:
  - leavitt-omega-has-an-explicit-distorted-target
---

Put `C=G_0*G_1*G_2*G_3`.  Reading cyclically after each stable-letter
occurrence gives four short involution corners

```text
a=a0,       b=b0,       c=c3,       d=d3,
```

and four long corners, displayed in `C`-syllable normal form,

```text
H=r0|e1|a2|c1|b3|d2|p3,
K=e0|a1|c0|b2|d1|p2|r3,
L=p0|r1|e2|a3|c2,
M=b1|d0|p1|r2|e3.                                  (CN1)
```

The source calculation gives

```text
<a,b>=V4.                                            (CN2)
```

For the target, `c,d` are involutions and

```text
(cd)^2=[c,d]=x_15(s0^2) !=1,
((cd)^2)^2=1.
```

Hence `<c,d>=D8` (the dihedral group of order eight).

Consider a reduced word in

```text
Q=V4(a,b)*D8(c,d)*F(H,K,L,M).                       (CN3)
```

A nontrivial `V4` or `D8` syllable inserted next to a long letter can delete
that long letter's endpoint only if one of

```text
r0,e0,p0 in V4(a0,b0),
p3,r3,e3 in D8(c3,d3),                               (CN4)
```

or its inverse analogue holds.  None does.  In the faithful Bergman chart,
the first group has four elements and the second eight; direct exact
comparison proves all exclusions in `(CN4)`.  Conceptually, `V4` is supported
on the source root packets, while `D8` is the three-root Heisenberg packet on
`13,35,15`; `p,r` have nontrivial permutation part and `e=x12(t1)` has the
wrong root support.

It remains to join two adjacent long letters with no intervening `(CN3)`
syllable.  For every pair from

```text
{H^+-1,K^+-1,L^+-1,M^+-1}
```

other than the eight inverse pairs, either the terminal and initial copies
are different or their product is nonidentity in that copy.  This is a finite
endpoint table, verified exactly by the artifact.  Thus an allowed join may
merge two `C` syllables but can never delete the merged syllable or initiate a
cancellation cascade.  Every reduced `(CN3)` word therefore expands to a
nonempty `G_0*G_1*G_2*G_3` normal form.  This proves `Q -> C` injective.

The argument is for arbitrary words.  In particular, the 48 exact identity
faces found in the reduced area-six census are not a bounded coincidence:
they are precisely short consequences of the abstract factors in `(CN3)`.
