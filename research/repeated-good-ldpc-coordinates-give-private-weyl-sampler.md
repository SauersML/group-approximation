---
rg: 2
id: repeated-good-ldpc-coordinates-give-private-weyl-sampler
kind: claim
title: Repeated good LDPC coordinates give a bounded-occurrence private Weyl sampler
distinct_from:
  very-low-rate-ldpc-private-weyl-sampler: that also asks for arbitrary-operator same-Hilbert rounding; this closes its scalar, matrix-dimension, bounded-occurrence, and class-two inputs only.
  independent-private-labels-have-growing-dual-distance: that rules out local checks for independently random labels; this samples from the coordinate multiset of a locally checkable code.
  generator-column-pauli-test-globalizes-but-does-not-pin-sites: that uses the complete product of two linear-size column sets; this replaces it by one private perfect matching after quadratic repetition.
---

Let `(C_r)` and `(D_r)` be binary linear codes of dimension `r`, length
`L=Theta(r)`, relative distance at least `delta>0`, and bounded-row/column-
weight parity presentations.  Repeat every coordinate `R=A r` times, where
`A` is a sufficiently large universal constant.  Replicate every local
parity context in every layer and connect corresponding coordinate copies
by fixed-degree expanders.

The resulting X and Z occurrence systems have

```text
N=LR=Theta(r^2)
```

coordinates, bounded occurrence degree, scalar kernel exactly `C_r` and
`D_r`, and unchanged coordinate-functional measures.  There are perfect
matchings with the following simultaneous properties.

1. Match the N X coordinates privately to the N Z coordinates.  For every
   `d<=r` and every pair of exact additive representations, the average
   matched Weyl defect is at least one universal `eta>0`.
2. On each side add a second, disjoint-pair commutation matching.  Every
   nonzero alternating form on the `r`-dimensional scalar kernel is nonzero
   on at least a universal positive fraction of those matched wedges.

Every occurrence participates in one mixed pair, at most one exterior-square
pair, boundedly many replicated local contexts, and boundedly many equality
edges.  Thus all selected ports have positive effective weight, total size is
`Theta(r^2)`, and no mixed pair is repeated.  Low mixed defect forces matrix
dimension greater than `r`; the same-basis overlay kills the full central
class-two contextual quotient.

The matchings can be selected recursively by finite real quantifier
elimination and lexicographic search.  This removes the sparse-inverse
pseudorandomness problem from `very-low-rate-ldpc-private-weyl-sampler`.
It does **not** prove that arbitrary near-perfect local-PVM representations
round to the scalar kernel on the same Hilbert space.  Exact contextual
quotients remaining after class two are genuinely nonnilpotent, and their
uniform exclusion/stability is the sole analytic code gate.

De la Salle's Pauli game does not supply that last gate.
`de-la-salle-pauli-game-starts-after-the-same-pvm-gate` checks Theorem 3.11
against this occurrence system: its two exponential-answer PVMs already give
exact additive `F_2^r` actions by Fourier transform, and the good codes only
globalize sampled mixed Weyl energy.  Compiling those PVMs into the repeated
coordinates recreates the same approximate parity/commutation rounding
problem.
