---
rg: 2
id: stw27-strict-comparison-non-pure-algebra-exists
kind: claim
title: A simple separable unital nuclear algebra with strict comparison that is not pure exists
root: true
distinct_from:
  stw99-problem-xxvii-comparison-vs-divisibility: that is the universal assertion of STW Problem XXVII; this is the negation of its part (1), recorded as its own root so that counterexample routes have a target.
  stw18-strict-comparison-non-z-stable-algebra-exists: that asks only for failure of Z-stability under strict comparison; this asks for failure of purity, which is stronger because Z-stable simple exact finite algebras are pure.
  stw23-rank-problem-counterexample-exists: that asks for one unrealized rank with no comparison hypothesis; this demands strict comparison, and forces failure of even approximate rank density.
artifacts:
  - research/artifacts/toms-winter-rank-density-firewall-2026-09-11.md
---

**OPEN.** There is a unital, simple, separable, nuclear, non-elementary,
stably finite C-star algebra `A` with strict comparison of positive elements,
with respect to its nonempty trace simplex, whose Cuntz semigroup is not almost
divisible, so that `A` is not pure.

Establishing this refutes part (1) of STW Problem XXVII, and hence the root
`stw99-problem-xxvii-comparison-vs-divisibility`, which lists this claim under
`refuted_by`.  By `stw18-counterexample-from-stw27-non-pure-algebra` it also
refutes Toms--Winter.

Everything any such `A` must satisfy:

- **Rank density fails.**  Some continuous strictly positive affine function
  on `T(A)` is not uniformly approximated by rank functions
  (`rank-density-and-strict-comparison-give-purity`).
- **Stable rank at least two, and no tracial approximate oscillation zero.**
  Pure is equivalent to stable rank one in the presence of strict comparison:
  Lin through `stw58-simple-pure-k1-bijective` in one direction, Thiel's rank
  realization in the other, then Fu--Lin.
- **Not AH** (`ah-algebras-realize-ranks-approximately`), **not real rank
  zero** (`stw27-real-rank-zero-almost-divisibility`), and **no compact
  finite-dimensional extreme tracial boundary**
  (`stw18-finite-trace-boundary-toms-winter`).

## Attempts

- **Through the K1-witness.**  A strict-comparison algebra that is not
  K1-injective is not pure (`stw18-k1-witness-constraints`).  Recorded as
  `stw27-counterexample-from-stw18-k1-witness` over the open witness claim.
  No candidate witness is known.
- **Approximately subhomogeneous building blocks.**  This is the natural
  non-AH class, and it still has locally finite nuclear dimension.  Rank
  density there is open without slow dimension growth.  In a recursive
  subhomogeneous block the attaching maps force the boundary values of every
  positive element.  Extending a twisted boundary field over a
  high-dimensional top cell with normalized rank within `delta` of a
  prescribed profile can be topologically obstructed when `delta` times the
  block size is below about half the cell dimension.  Whether this gluing
  obstruction can survive in a simple limit together with strict comparison
  is the live question for this root; see
  `simple-unital-ash-algebras-realize-ranks-approximately` once landed.
