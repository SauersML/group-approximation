---
rg: 2
id: compression-codes-are-small-generating-partitions
kind: claim
title: An almost-everywhere injective equivariant code into B symbols exists exactly when the Bernoulli shift has a generating partition with |B| pieces
distinct_from:
  measurable-alphabet-compression-over-leavitt-units: that is the open existence question over the Leavitt units; this is a general exact reformulation of what such a code is, valid over every countably infinite group.
  leavitt-units-have-zero-rokhlin-entropy-supremum: that is an entropy statement about every free action; this equates coding objects with generating partitions at the same alphabet size, with no generator theorem imported.
artifacts:
  - research/artifacts/defect-coupled-routed-codes-2026-09-12.md
---

Let `G` be countably infinite and `A, B` finite. There is a Borel equivariant `tau: A^G -> B^G`
injective on a conull set iff the uniform Bernoulli shift `(A^G, mu_A)` has a Borel partition with
`|B|` pieces whose translates generate the Borel sigma-algebra modulo null sets.

The forward direction is Proposition 1 of the compression artifact. The converse takes the name map
`tau(x)(g) = b` iff `g^-1.x` lies in the `b`-piece. Equivariance is immediate, and a countable separating
family approximated inside the generated sigma-algebra shows injectivity on a conull set.

So designing a compression over `U = L_(F_2)(1,2)^x` means designing a generating partition with fewer
pieces than the base alphabet. The converse needs no generator theorem, unlike the deficit form in the
compression artifact's Remark.

Proof: Section 3 of the artifact, route `compression-small-generating-partitions-proof`.
