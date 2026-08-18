---
rg: 2
id: hyperlinear-implies-sofic-via-cpsd-face-collapse
kind: route
title: Conic feasibility on the group-table face, with sign tests as the interface
target: hyperlinear-implies-sofic
requires:
  - group-table-cpsd-cp-face-collapse
  - random-hyperplane-hs-binaryization
---

Let `G` be hyperlinear, `F ⊂ G` finite with table `T`, and `eps > 0`.

*From microstate to conic point.*  The correlation system of
`group-table-cpsd-cp-face-collapse` is a constraint system in Boolean
observables, so the microstate has to be read out as bits.  That is what
`random-hyperplane-hs-binaryization` provides, dimension-free in both
directions: a tested product with HS defect `delta` yields sign observables
disagreeing with probability at most `delta/2`, so the correlation data of the
microstate is feasible for the quantum cone up to `O(delta)`; and a
trace-separated pair disagrees with probability at least `d_2^2/(2 pi)`, which
keeps the point on the regular-character face rather than collapsing to a
degenerate one.  Both bounds are independent of the matrix dimension, which is
what lets `delta` be chosen after `eps`.

*From conic point to permutation model.*  By the collapse, the limit point lies
in the closure of the classical face, whose points are, by construction of the
encoding, mixtures of finite partial actions of `T` by bijections; taking a
point of the mixture with the right marginals and repairing the partial
bijections to permutations gives a model of `T` with Hamming defect `< eps`.
Hence `G` is sofic.

This is a reduction, not a rename: the premise is a statement about two convex
cones attached to one finite table, it mentions neither groups nor sofic
approximations, and it can fail (by an exposed dual functional) in a way that
would be visible on a single table.  The interface lemma is doing genuine work
— without a dimension-free HS-to-Boolean conversion there is no way to place a
microstate in the cone at all, since the cone's variables are correlations of
±1 observables and the hypothesis is a norm bound.
