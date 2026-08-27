---
rg: 2
id: agent-first-hit-schur-two-cell-regular-model-proof
kind: route
title: Move the forbidden Schur phase to multiplicity and realize the whole cell by a finite semidirect packet
target: agent-first-hit-one-schur-two-cell-is-regular-absorbed
requires:
  - schur-packet-flips-realize-predicate-cocycle
  - commuting-automorphism-cocycle-forces-multiplicity
  - fixed-d8-holonomy-has-no-determinant-density
  - projective-holonomy-rank-forces-exponential-multiplicity
---

Schur's lemma gives `(SRA3)`.  Since the packet implementers anticommute,
the global stable letters commute exactly if and only if their multiplicity
factors anticommute, proving `(SRA4)` and the parity condition.

The automorphisms commute as actual automorphisms of `B_f`, not merely
projectively on one simple.  Hence they define the finite semidirect product
`(SRA5)`.  Its regular permutation implementation realizes `(SRA1)` and
preserves the negative central corner, proving the marked countermodel.

On odd multiplicity, the block-diagonal Pauli construction leaves one scalar
coordinate.  The multiplicative commutator equals `-I` rather than `I` only
on that coordinate, giving `(SRA6)`.  Symplectic reduction of a rank-`2r`
binary cocycle gives the divisor `2^r`; the same block-plus-remainder argument
gives the stated `O_r(2^r/m)` repair.

