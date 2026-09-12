---
rg: 2
id: stw84-bounded-overlap-fourier-gap
kind: claim
title: Bounded-overlap duplication cannot repair weighted Fourier rows
distinct_from:
  stw84-bounded-coordinate-colour-gap: that theorem assigns every Fourier coordinate to one colour and uses a balanced split inside the largest colour; the present theorem permits every coordinate to occur in every colour and obstructs all bounded internal overlap profiles by a norm-concentration argument.
artifacts:
  - research/artifacts/stw84-bounded-overlap-duplication-firewall-2026-08-30.md
---

Let `A` be a unital C-star algebra, let `h in A` be a norm-one positive
contraction, and put

```text
Lambda_(h,n)(z_1,...,z_n)=n^(-1)(sum_i z_i)h.          (BOD1)
```

Let `T_1,...,T_r:C^n->A` be c.p.c. maps, write

```text
x_(c,i)=T_c(e_i),       X_c=T_c(1)=sum_i x_(c,i),
Psi=sum_c T_c,                                          (BOD2)
```

and suppose that, for some `M>=1`, every colour satisfies the bounded
overlap inequality

```text
||X_c|| <= M max_i ||x_(c,i)||.                        (BOD3)
```

Then, whenever `n>rM`,

```text
||Lambda_(h,n)-Psi||
 >= (1-rM/n)/(rM+1).                                  (BOD4)
```

In particular, if `n>=2rM`, the distance is at least

```text
1/(2(rM+1)).                                           (BOD5)
```

Condition `(BOD3)` holds with `M=1` when each `T_c` is order zero.  More
generally, it holds when, inside each colour, the indices can be partitioned
into `M` classes such that the positive elements `x_(c,i)` belonging to one
class are pairwise orthogonal.  Therefore `(BOD4)` covers:

* arbitrary duplication of every Fourier coordinate among a fixed number
  of order-zero return colours;
* scalar Fejer or tent weights followed by order-zero maps;
* two-grid shifts and graph-coloured band returns with uniformly bounded
  orthogonality chromatic number (in particular, bounded interval-overlap
  depth);
* scalar diagonal restrictions of coefficient-valued versions of the same
  constructions.

Indeed, diagonal scalar weighting before an order-zero return remains order
zero, even when every coordinate is present in several colours.

For the canonical weighted Fourier row `Theta_(h,n)`, the restriction to
the scalar diagonal is `(BOD1)`.  Hence no fixed values of `r` and `M` can
give a convergent repair of that row as the tolerance tends to zero.  A
successful non-coordinate factorization must make the internal overlap
depth of the composed colour maps grow with the Fourier window, or use an
incoming c.p. map which mixes diagonal coordinates so thoroughly that
`(BOD3)` fails.  Nuclear dimension permits that remaining escape, so the
theorem is not a lower bound on the nuclear dimension of the augmentation
ideal.
