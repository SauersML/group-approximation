---
title: STW XX checkpoint --- point-dominated diagonal maps give uniform Gamma (2026-08-30)
---

## Setup

For a composite diagonal map between homogeneous stages, let `L_(n,m)`
be its total eigenvalue multiplicity and `C_(n,m)` the number of
nonconstant coordinate eigenmaps.  The other eigenmaps are constant point
evaluations, not necessarily repeated.

The new theorem proves uniform property Gamma whenever, from every fixed
stage, one can pass along a cofinal subsequence so that

`L_(n,m)->infinity`,  `C_(n,m)/L_(n,m)->0`.

This is the point-dominated or vanishing-coordinate-weight diagonal
regime.

## Why distinct point evaluations can still be halved

A block-scalar projection commutes exactly with the image of the earlier
stage, regardless of whether its eigenvalue maps agree.  The only issue is
uniform trace splitting.  For a finite test set `F`, each point evaluation
contributes the scalar vector

`(tr(a(x_i)))_(a in F)`.

Randomly assigning these vectors to `k` colours gives, for each colour,
discrepancy at most `sqrt(k|F|P)` for a suitable colouring, where `P` is
the number of point blocks.  After normalization by `L`, this is at most
`sqrt(k|F|/L)`.  The coordinate blocks depend on the later base point and
cannot be balanced by this finite vector argument, but their entire
worst-case contribution is at most `C/L`.  Thus the error is

`sqrt(k|F|P)/L + C/L -> 0`.

Diagonalizing over stages and finite sets gives norm-central orthogonal
partitions of unity whose traces split uniformly.  In the two-colour case
`h=2p-1` is a central selfadjoint unitary with uniformly vanishing mixed
traces `tau(ah)`.

## Relation to the open Villadsen regime

The theorem is unconditional but does not settle the exotic first-type
examples highlighted in Problem XX.  In those systems the composite
identity-coordinate proportion has a positive asymptotic lower bound
`w>0`; the coordinate projections are nonconstant and counted with
multiplicity, so `C_(n,m)/L_(n,m)` does not vanish.  This pinpoints the
remaining obstruction: point-evaluation complexity, including a wild
trace simplex, is not itself a barrier.  The only mass not handled by
finite-dimensional discrepancy is the positive nonconstant-coordinate
mass.

The proof is internal to the diagonal model and imports no classification,
strict-comparison, or trace-boundary theorem.  It complements the cached
Elliott--Niu obstruction: their negative result for the canonical Cartan
lies in the positive-coordinate-weight regime, while the block projections
constructed here solve the vanishing-coordinate-weight regime directly.
