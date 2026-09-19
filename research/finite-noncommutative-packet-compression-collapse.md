---
rg: 2
id: finite-noncommutative-packet-compression-collapse
kind: claim
title: A finite noncommutative packet cannot retain a child-only symmetry under Kazhdan self-compression
distinct_from:
  compression-torsion-collapse: That theorem requires the entire orbit of the finite-order witness to commute pairwise; here the packet is an arbitrary finite group and the orbit may be maximally noncommutative.
  semisimple-packet-multiplicity-collapse: That open claim treats an increasing locally finite-dimensional orbit algebra; this theorem is the fixed finite-packet case, where one tail exactification suffices and no growing-window bookkeeping is needed.
  finite-memory-self-hash-non-mf: That open route seeks an operator-norm checksum for a moving infinite self-copy tape; this theorem avoids moving addresses by using a fixed finite packet and self-normalizing rank weight.
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
  - GroupApproximation/Sofic/ScaledKazhdanTransport.lean
  - GroupApproximation/Sofic/InvolutionRankMass.lean
---

Let `W` be countable, let `L<=W` be finitely generated and Kazhdan, and let `sLs^(-1)<=L`.  Let `K<=W` be a
finite subgroup normalized by `L`, and let `k in K` be fixed by
`sLs^(-1)`.  Then every homomorphism from `W` to the unitary group of a norm
matrix corona identifies `k` with every `L`-conjugate.  Equivalently every
commutator `[g,k]`, `g in L`, belongs to the operator-MF radical.

The proof exactifies `K`, polar-corrects covariance, weights the displacement
cocycle by the integer sum of generator ranks, applies Delorme property-(T),
and uses `scaled-kazhdan-transport` to return the primitive through the
one-sided compressor.  No pairwise commutation is used.

**FORMALIZATION STATUS.**  This is established in Cairn by the complete
paper-level route and the cited audit.  The arbitrary-weight transport and
rank/mass inequalities are kernel-checked in the linked Lean modules; the
finite-packet exactification, covariance wrapper, weighted cocycle assembly,
and their endpoint theorem do not yet have Lean declarations.
