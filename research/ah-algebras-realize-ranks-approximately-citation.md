---
rg: 2
id: ah-algebras-realize-ranks-approximately-citation
kind: route
title: Read approximate rank realization out of the first half of Brown--Perera--Toms Theorem 5.3
target: ah-algebras-realize-ranks-approximately
requires: []
artifacts:
  - research/artifacts/toms-winter-rank-density-firewall-2026-09-11.md
---

**Established by citation, with the hypothesis scope checked from the source.**
N. P. Brown, F. Perera, A. S. Toms, *The Cuntz semigroup, the Elliott
conjecture, and dimension functions on C*-algebras*, J. reine angew. Math.
621 (2008), arXiv:math/0609182, pages 11--15 of the arXiv version, read in
this lane:

- **Proposition 5.1.**  In a simple `A` with dense increasing union of
  subalgebras, every continuous strictly positive affine function on `T(A)` is
  within `eps` of `tau -> tau(a)` for some positive `a` in a finite stage.
- **Lemma 5.2.**  For homogeneous `B = p(C(X) tensor K)p` of rank `n` and
  continuous affine `0 <= g <= 1`, some `a in M_infty(B)_+` has
  `0 <= g - d(a) <= 1/n`.  The element is a direct sum of bump functions times
  one fixed trivial rank-one projection.
- **Proof of Theorem 5.3, first part.**  Pull `f` back to a stage, compress so
  that `1/min_j rank(p_(i,j)) << eps`, apply Lemma 5.2 in each summand, and
  push forward.  This gives `0 <= f - d(a_i) <= eps_i/2` on `T(A)`.

The stable rank one and strict comparison hypotheses of Theorem 5.3 are used
only afterwards, through Theorem 4.4 and Corollary 4.7, to upgrade the
approximating sequence to an exact preimage.  So the approximation statement
holds for every unital simple separable infinite-dimensional AH algebra.
Bounded `f` with values above 1 is handled by approximating `f/M` and taking
an `M`-fold direct sum.  Details are in the linked artifact.
