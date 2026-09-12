---
rg: 2
id: jacobson-shift-block-permutation-models-have-a-gap
kind: claim
title: Recursive Jacobson models permuting blocks of bounded size have a positive matrix gap
distinct_from:
  bounded-block-jacobson-microstates-also-collapse: that bounds the sizes of irreducible blocks of the entire generated algebra; this permits arbitrary permutations of bounded-size fibers and hence arbitrarily large irreducible representations of that algebra.
  jacobson-shift-monomial-models-have-a-uniform-gap: that treats one-dimensional fibers and an explicit norm neighborhood; this permits higher-dimensional fibers with a gap depending on their fixed maximum dimension.
artifacts:
  - research/artifacts/jacobson-shift-exact-collapse-and-monomial-gap-2026-09-08.md
---

For every fixed positive integer `m`, there is `kappa_m>0` such that
admissible data in `jacobson-shift-gap-characterizes-mark-collapse`
have maximum mixed error at least `kappa_m` whenever all matrices
of the two exact finite packets and the stable letter permute the
blocks of one orthogonal decomposition of the whole representation
space, with every block of dimension at most `m`.

The total dimension and number of blocks are arbitrary. No explicit
value of `kappa_m` is claimed for `m>1`.

Small mixed error makes the finite block-permutation quotient exact;
it kills the head and hence the six-coordinate group `K`. Its
conjugates therefore preserve each block individually. Conjugacy of
adjacent head roots inside these exact `K` packets propagates a retained
head through every shifted copy on one fixed block. Compactness in
that bounded-dimensional block would turn errors tending to zero into
more than `m/2` exact commuting nontrivial perfect-group factors, which
is impossible.

No bound uniform in `m` is established. Since every matrix tuple fits
the one-block class with `m` equal to its dimension, this dependence
prevents the result from settling unrestricted `gamma_shift`.

DERIVATION
jacobson-shift-active-block-compactness-proof
