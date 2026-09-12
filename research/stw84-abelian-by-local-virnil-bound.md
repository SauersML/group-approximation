---
rg: 2
id: stw84-abelian-by-local-virnil-bound
kind: claim
title: Finite-rank abelian-by-uniformly-locally-virtually-nilpotent groups have finite nuclear dimension
distinct_from:
  stw84-locally-virtually-polycyclic-uniform-hirsch: the semidirect product here need not be locally virtually polycyclic; already BS(1,n) is finitely generated but not virtually polycyclic.
  stw84-kernel-finite-locally-finite-by-abelian-computation: the normal group here is abelian and can be torsion-free and infinitely generated, rather than locally finite with finite intersections.
  stw84-locally-finite-lamp-wreath-bound: the normal group here has finite positive rational rank and the action can be expanding rather than a Bernoulli shift on a locally finite base.
artifacts:
  - research/artifacts/stw84-abelian-by-local-virnil-audit-2026-08-30.md
---

Let `A` be a countable abelian group of finite rational rank

```text
r=dim_Q(Q tensor_Z A),
```

and let a countable group `H` act on `A` by automorphisms.  Assume every
finitely generated subgroup `V<=H` is virtually nilpotent and

```text
s=sup{h(V): V<=H finitely generated}<infinity.          (ALN1)
```

Then `G=A rtimes H` is amenable and, for `s>=1`,

```text
dim_nuc(C*(G))
    <= 2 * s! * 9^(s^2) * (r+1)^2 < infinity.           (ALN2)
```

If `s=0`, then `H` is locally finite and the sharper estimate is

```text
dim_nuc(C*(G)) <= r.                                    (ALN3)
```

The universal abelianization lower bound makes this a two-sided estimate:

```text
rank_Q(A/[A,H]) + rank_Q(H_ab)
    <= dim_nuc(C*(G)).                                  (ALN4)
```

There is a substantially sharper cyclic limit.  If `H` is locally cyclic,
then

```text
dim_nuc(C*(G)) <= 2r^2+6r+4;                            (ALN5)
```

if this locally cyclic `H` is torsion, `(ALN3)` applies instead.

For example, for every integer `n>=2`,

```text
BS(1,n) = Z[1/n] rtimes_(x |-> nx) Z
```

is covered with

```text
1 <= dim_nuc(C*(BS(1,n))) <= 12.                        (ALN6)
```

These groups are finitely generated but not virtually polycyclic, so `(ALN6)`
does not follow from the virtually-polycyclic or uniform-local-polycyclic
lanes.
