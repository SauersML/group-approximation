---
rg: 2
id: stw27-counterexample-via-ash-gluing-rank-gap
kind: route
title: An ASH algebra with strict comparison and a rank gap refutes part (1) of Problem XXVII
target: stw27-strict-comparison-non-pure-algebra-exists
requires: [ash-strict-comparison-rank-gap-algebra-exists, thiel-stable-rank-one-ranks-close-purity-with-comparison]
artifacts:
  - research/artifacts/toms-winter-rank-density-firewall-2026-09-11.md
---

Let `A` be the algebra from the first prerequisite.  It is unital, simple,
separable, infinite-dimensional and ASH, hence nuclear, and it has strict
comparison.  `T(A)` is nonempty, because every subhomogeneous stage has
traces and `T(A)` is their inverse limit.  So `A` is stably finite.

Suppose `A` were pure.

1. H. Lin, *Strict comparison and stable rank one*, J. Funct. Anal. 289 (2025),
   111065, Theorem 3.6, as quoted in `stw58-simple-pure-k1-bijective-proof`:
   a unital simple pure algebra is purely infinite or has stable rank one.
   Stable finiteness excludes the first case, so `A` has stable rank one.
2. The second prerequisite (Thiel) then realizes every strictly positive lower
   semicontinuous affine function on `QT(A) = T(A)` exactly as a rank.  In
   particular `f` is exactly realized, contradicting the rank gap.

So `A` is not pure while having strict comparison, which is the target.

This route is invalidated once
`simple-unital-ash-algebras-realize-ranks-approximately` is established,
because that claim excludes its premise.
