---
rg: 2
id: odometer-prefix-index-and-balanced-labels-proof
kind: route
title: Compute near index leaf by leaf and generate every zero-sum table from a single balanced exchange
target: odometer-prefix-groups-have-fg-index-kernels
requires: []
artifacts:
  - research/artifacts/boone-higman-arithmetic-odometer-model-2026-09-08.md
---

Use least-significant-first h-adic digits 0,...,h-1. The odometer
has wreath recursion a=(1,...,1,a)*(0 1 ... h-1). Its inverse
has the analogous borrowing recursion. These are finite-state
automorphisms with only one active section at every depth.
Thus <a> is a bounded automata group. By
[Belk--Hyde--Matucci, Theorem 2.12](https://arxiv.org/html/2407.03149v1#S2.SS3),
B=V_(h,r)(<a>) has type F_infinity. Taking the trivial automata
group in the same theorem also gives finite generation of V_(h,r).

## The faithful near action and its index

A prefix-table branch with source root i, prefix u of length k,
target root j, prefix v of length l, and section a^c acts by

    i+r*u+r*h^k*t  ->  j+r*v+r*h^l*(t+c).

Here u and v denote the standard integer values of their prefixes,
so 0<=u<h^k and 0<=v<h^l. The source and target prefix partitions
partition N into the corresponding progressions with t>=0. On a
branch with c>=0, the map misses the first c points of its target
progression. With c<0, discard the first -c points of its source
progression, and its target progression is then exhausted. This
gives a cofinite bijection with index c on that branch, under the
convention missing range minus missing domain. Summing gives chi.

All elements of B therefore induce near permutations, and composition
of the Cantor maps induces composition of the near permutations.
The embedding of N is dense, and remains dense after removing
finitely many points. If a B element induces the identity near
permutation, it fixes that dense set and hence is identity on the
Cantor set. This proves faithfulness. The usual additivity of near
index proves that chi is a well-defined homomorphism, independent
of the prefix table. Alternatively, refining a branch replaces c
by the h carry labels floor((d+c)/h), d=0,...,h-1, whose sum is c.
A localized odometer on a proper cone has chi=1, proving surjectivity.

## Generate the balanced labels

Choose disjoint cones U,W whose union is proper. Let t exchange
them by

    U*z -> W*a(z),       W*z -> U*a^-1(z),

and fix the complement. This lies in B, is an involution, and
has chi=0. Multiplying by the pure prefix exchange of U,W gives
opposite localized odometers on the two cones, with charges -1,+1.

For any other ordered pair of disjoint cones with proper union,
an element of V_(h,r) carries U,W to that pair by pure prefix maps.
To extend the two prescribed maps, partition the two nonempty
complements into cones. Their leaf counts are equal modulo h-1;
refine them until the counts agree and match the remaining leaves.
Thus <V_(h,r),t> contains the difference of localized odometers
on every such pair.

Now take b with chi(b)=0. Refine its table until it has at least
three leaves, retaining the sum of its carry labels. Factor it as
a pure prefix element followed by the leafwise odometer powers on
the target partition. Their exponents c_1,...,c_m sum to zero.
Each pair of target leaves has proper union. Writing the leafwise
map as the product, for i<m, of opposite powers c_i,-c_i on leaf
i and leaf m expresses it using the differences just constructed.
The local maps on disjoint leaves commute, so the product has
exactly the required labels. Hence ker(chi)=<V_(h,r),t>, which is
finitely generated. This argument supplies no finite presentation
for that kernel.
