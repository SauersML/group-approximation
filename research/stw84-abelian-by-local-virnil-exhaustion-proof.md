---
rg: 2
id: stw84-abelian-by-local-virnil-exhaustion-proof
kind: route
title: Dualize the abelian kernel and exhaust the acting group with uniform long-thin bounds
target: stw84-abelian-by-local-virnil-bound
requires:
  - hirshberg-wu-virtually-nilpotent-action-bound
  - hirshberg-wu-cyclic-action-bound
  - stw84-directed-union-uniform-bound
  - stw84-abelianization-rank-lower-bound
artifacts:
  - research/artifacts/stw84-abelian-by-local-virnil-audit-2026-08-30.md
---

Put `X=A_hat`.  Since `A` is countable, `X` is compact metrizable.  Fourier
transform and Pontryagin dimension theory give

```text
C*(A)=C(X),                 dim(X)=rank_Q(A)=r.          (1)
```

The action of `H` on `A` dualizes to an action on `X`.  Since `A` and `H`
are amenable, so is their extension `G`; full and reduced crossed products
agree and the canonical covariant representations give

```text
C*(A rtimes H)=C(X) rtimes H.                           (2)
```

## Uniform virtually nilpotent exhaustion

Choose an increasing exhaustion

```text
V_1 <= V_2 <= ... <= H
```

by finitely generated subgroups and set `G_j=A rtimes V_j`.  Each `V_j` is
virtually nilpotent.  If `h_j=h(V_j)` and `d_j=d(V_j)` is its polynomial
growth degree, the Bass--Guivarc'h formula gives

```text
d_j <= h_j^2 <= s^2.                                   (3)
```

Indeed, after passage to a finite-index nilpotent subgroup with lower-central
series ranks `a_i`, one has `h_j=sum_i a_i` and `d_j=sum_i i*a_i`; the
nilpotency class is at most `h_j`, giving `(3)`.

By `hirshberg-wu-virtually-nilpotent-action-bound`, `(1)` and `(2)`,

```text
dim_nuc(C*(G_j))
 <= 2 * h_j! * 9^d_j * (r+1)^2
 <= 2 * s! * 9^(s^2) * (r+1)^2.                        (4)
```

The union of the `G_j` is `G`.  The inclusions of their reduced group
C-star-algebras are injective, and amenability identifies them with the full
algebras.  Thus `stw84-directed-union-uniform-bound` applied to `(4)` proves
`(ALN2)`.

If `s=0`, every finitely generated subgroup of `H` is finite, so `H` is
locally finite.  Each `G_j` is abelian-by-finite and every finitely generated
subgroup of `G_j` is virtually abelian of Hirsch length at most `r`.
Equivalently, one can apply `(HWC2)` directly to
`C*(G_j)=C(X) rtimes V_j`.  In either case

```text
dim_nuc(C*(G_j))<=r
```

uniformly, and the same limit argument proves `(ALN3)`.

## The cyclic improvement

Suppose `H` is locally cyclic.  The exhaustion can be chosen with every
`V_j` cyclic.  If `V_j` is finite, `(HWC2)` gives dimension at most `r`; if
`V_j` is infinite, it is isomorphic to `Z` and `(HWC1)` gives dimension at
most `2r^2+6r+4`.  These bounds are independent of the order, generator, and
action.  The directed-limit theorem proves `(ALN5)`.  If `H` is torsion, all
the stages are finite and the sharper bound `(ALN3)` remains valid.

## Lower bound and the expanding example

For a split semidirect product with abelian kernel, commutators give the
canonical decomposition

```text
(A rtimes H)_ab = A/[A,H] direct_sum H_ab.              (5)
```

Applying `stw84-abelianization-rank-lower-bound` to `(5)` proves `(ALN4)`.

Finally take `A=Z[1/n]`, `H=Z`, with the generator acting by multiplication
by `n`.  This is `BS(1,n)`.  Here `r=s=1`, so `(ALN5)` gives the upper bound
`12`.  In `(5)`, the `H_ab=Z` summand gives the lower bound `1`.  The normal
abelian subgroup `Z[1/n]` is not finitely generated.  More strongly, if
`K<=BS(1,n)` has finite index, then `K intersection Z[1/n]` has finite index
in `Z[1/n]` and is still not finitely generated: it contains
`m Z[1/n]` for the finite index `m`, and that subgroup is isomorphic to
`Z[1/n]`; if the intersection were finitely generated abelian, all of its
subgroups would be finitely generated.  A polycyclic group has every
subgroup finitely generated, so no
finite-index `K` can be polycyclic.  This verifies the separation asserted
in the claim.
