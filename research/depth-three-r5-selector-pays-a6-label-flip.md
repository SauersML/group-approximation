---
rg: 2
id: depth-three-r5-selector-pays-a6-label-flip
kind: claim
title: One asymmetric depth-three R5 selector pays the A6 label flip exactly
distinct_from:
  depth-three-bq-arm-expansion-is-equivariant-under-label-flip: that proves the canonical R2/R3 expansions are transported wholesale by the label flip; this supplies an additional disjoint-support cell which is deliberately not invariant under that flip.
  bare-r5-a6-collision-does-not-synchronize-shared-labels: that uses R5 only on the two nonshared Carmichael leaves and therefore mentions neither common label; this R5 instance contains a shared-label arm and a selector meeting its false alternative.
  shared-endpoint-r2-r3-anchor-has-linear-seam-bound: that cancels literally common endpoints by the triangle inequality; this is a finite-permutation character identity which detects the wrong endpoint without first making it common.
---

Keep the depth-three labels

```text
p=000, q=001, i=010, j=011, k=100
```

and put, in the finite leaf permutation group,

```text
c_i=(i p q),       c_j=(j p q),
s_i=(i p),         s_j=(j p),         z=(j k).                   (RSE1)
```

Then `s_i` and `z` have disjoint support, whereas `s_j` and `z` overlap in
one letter.  Hence

```text
[s_i,z]=1,                 [s_j,z] is a three-cycle.              (RSE2)
```

The element `c_i^(-1)c_j` is also a three-cycle.  Therefore for every
finite-dimensional unitary representation `pi` of the six-letter symmetric
group, with normalized matrix trace,

```text
||pi(c_i)-pi(c_j)||_2^2
 =||pi(c_i^(-1)c_j)-I||_2^2
 =||pi([s_j,z])-I||_2^2.                                         (RSE3)
```

Moreover `[s_i,z]=1` is a literal conjugate of the Bleak--Quick R5 relator:
the two ordered pairs of disjoint swaps

```text
((000 010),(10 110))      and      ((010 000),(011 100))          (RSE4)
```

are conjugate in `V` after refining only the fixed complement.  Thus a
single R5 cell selected asymmetrically by the actual address detects exactly
the five-dimensional A6 label flip which the nonshared R5 collision and the
canonical R2/R3 triangles miss.

This is an exact finite-packet statement, not yet the Thompson seam theorem.
To use `(RSE3)` on approximate contextual words one must retain the same
selector `z` while exactifying the bounded six-letter packet, or prove the
corresponding approximate character inequality directly.  The affine/private
gauge problem is precisely whether that selector occurrence can be kept
literal in both adjacent charts.

