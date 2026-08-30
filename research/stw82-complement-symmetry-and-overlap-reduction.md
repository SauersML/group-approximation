---
rg: 2
id: stw82-complement-symmetry-and-overlap-reduction
kind: claim
title: Complement symmetry reduces multiplier-projection adjunction to two proper overlapping support ideals
distinct_from:
  stw82-split-af-is-one-multiplier-projection-problem: that reduction treats fullness of the adjoined projection p; the present theorem proves exact p versus 1-p symmetry and therefore also handles a full complementary projection.
  stw82-quasicentral-support-thickening-preserves-dimension: that theorem crosses a proper noncomplemented support through a quasidiagonal residual extension; the present theorem applies with no quasidiagonality when the complementary projection is full.
artifacts:
  - research/artifacts/stw82-complement-symmetry-overlap-audit-2026-08-30.md
---

Let `A` be a C-star algebra and `p in M(A)` a projection.  Put `q=1-p`.
Then

```text
dim_nuc(A+C p)=dim_nuc(A+C q).                           (CSO1)
```

Indeed, the two algebras have the same minimal unitization inside `M(A)`:

```text
(A+C p)~=A+C1+C p=A+C1+C q=(A+C q)~.                   (CSO2)
```

Nuclear dimension is invariant under minimal unitization, proving `(CSO1)`.

Consequently, if `A` is sigma-unital and either `p` or `1-p` is full as a
multiplier projection of `A`, then

```text
dim_nuc(A+C p)=dim_nuc(A).                              (CSO3)
```

The case where `p` is full is the established full-corner theorem.  If
`q=1-p` is full, apply that theorem to `A+Cq` and then use `(CSO1)`.
Thus a counterexample must have **both** complementary multiplier
projections nonfull.

There is also an exact normal form for that remaining case.  Assume neither
`p` nor `q` belongs to `A`, since those cases reduce respectively to `A` or
its minimal unitization.  Set

```text
L=closure(ApA),       R=closure(AqA),       I=L intersect R.
```

Then

```text
L+R=A,                                                    (CSO4)
K/I is isomorphic to (A/L) direct_sum (A/R)~,             (CSO5)
dim_nuc(K/I)<=dim_nuc(A),       where K=A+C p.             (CSO6)
```

Moreover both `p` and `q` restrict to full complementary projections in
`M(I)`.  Hence every still-unresolved multiplier-projection adjunction is
concentrated on a nonzero overlap ideal on which both sides are full; after
removing that overlap, the middle algebra is merely a direct sum of one
quotient and the unitization of the other.  If `I=0`, `(CSO5)` already gives
the desired equality, recovering the complemented-support case.

This positive theorem genuinely crosses the previous nonquasidiagonal
firewall.  In the stabilized Toeplitz example

```text
A=T tensor K,
p=(1-SS*) tensor 1,
```

the support of `p` is proper, essential, noncomplemented, and its residual
extension after adjoining `p` has nonzero index and is not quasidiagonal.
Nevertheless `q=SS* tensor 1` is full, so `(CSO3)` proves the
multiplier-projection formula directly.
