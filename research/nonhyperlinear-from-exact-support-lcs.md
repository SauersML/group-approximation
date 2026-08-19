---
rg: 2
id: nonhyperlinear-from-exact-support-lcs
kind: route
title: Exact-support LCS sparsification yields an explicit nonhyperlinear solution group
target: non-hyperlinear-group
requires:
  - mipstar-bcs-tracial-nonru-exists
  - exact-support-relator-sparsification
  - bcs-to-lcs-exact-support-gap
  - explicit-exact-support-lcs-witness
artifacts:
  - research/artifacts/lcs-exact-support-sparsification-2026-08-18.md
---

`mipstar-bcs-tracial-nonru-exists` supplies the unconditional noncommutative
source gap from `MIP*=RE`.  The open compiler theorem
`bcs-to-lcs-exact-support-gap` asks for less than a perfectly complete
BCS-to-LCS reduction: only that the mass of linear checks satisfied **exactly**
by one tracial assignment exceed the maximum enlarged-threshold mass
satisfiable by a finite-dimensional assignment keeping the central mark
separated.

The established theorem `exact-support-relator-sparsification` then samples a
finite submenu whose solution-group mark `J` is nontrivial in an exact tracial
representation but trivial in approximate representations.  By the
Paddock--Slofstra solution-group criterion this presentation is
nonhyperlinear.  `explicit-exact-support-lcs-witness` freezes one actual linear
system and its constants, upgrading the probabilistic existence conclusion to
the primary goal's explicit witness.

This route does not require perfect completeness of the whole LCS compiler,
property-(T) stability, commutant reconstruction, a Leavitt decoder, or a
nonlocal game as the final object.  The sole new mathematics is the
exact-support/soundness strict inequality for a source-specific linearization.
