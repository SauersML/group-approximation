---
rg: 2
id: repeated-ldpc-adjoint-face-hamiltonian-gap
kind: claim
title: The repeated LDPC face pinchings have a uniform adjoint syndrome gap
distinct_from:
  unique-neighbor-ldpc-checks-force-dense-noncommutation: that gives exact support expansion only for coordinate commutator rows; this asks for a quadratic spectral gap on all of L2 of every matrix model.
  adjoint-parity-defects-form-tanner-fundamental-cone: that supplies local cone inequalities for Q_j test vectors; this asks for distance to the full common commutant.
  sequential-pinchings-have-sharp-linear-disturbance-loss: that refutes ungapped coordinate-by-coordinate pinching; this is the parity-aware gap that would repair it.
---

OPEN.  For the bounded-width face PVMs of the repeated good-LDPC occurrence
system, prove `(GFP3)` from
`gapped-face-pinchings-give-same-hilbert-code-pvm-rounding` with one universal
`gamma>0`, uniformly over all tracial matrix representations satisfying the
local face relations.

This is a genuinely operator-valued strengthening of classical LTC or
unique-neighbor expansion.  Classical soundness proves the corresponding
gap only after all coordinate algebras commute and the problem decomposes
into scalar words.  The desired inequality acts on arbitrary `X in L_2(M)`
and must control rotations among multiplicity/character sectors.  The
fundamental-cone theorem verifies necessary magnitude inequalities on the
special vectors `X=Q_j`, but its homogeneous pseudoweight bounds do not yet
prove distance to the common commutant.

Bounded overlap alone cannot imply the gap:
`sequential-pinchings-have-sharp-linear-disturbance-loss` exhibits an
ungapped sparse Clifford cycle.  Local codeword PVMs and overlap consistency
alone also cannot imply it at positive rate, by
`positive-rate-tanner-tests-have-contextual-models`.  The possible positive
input is the joint use of low rate, LTC soundness, and the complete-pair
overlay; no existing Cairn theorem supplies that operator gap.

`uniform-conjugation-kazhdan-gap-gives-face-hamiltonian-gap` gives an exact
group-theoretic sufficient condition.  A uniform normalized property-T gap
for the homogeneous LCS face groups would close this node.  This does not
help exactify approximate face tables: the Kazhdan inequality applies only
after `repeated-ldpc-shared-face-marginal-synchronization` has produced an
exact group representation.
