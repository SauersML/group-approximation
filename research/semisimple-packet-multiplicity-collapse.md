---
rg: 2
id: semisimple-packet-multiplicity-collapse
kind: claim
title: Compression collapse for semisimple packets via self-normalized multiplicity defects
distinct_from:
  compression-torsion-collapse: That established claim needs the orbit images to commute pairwise, so its discrete invariant is a joint spectral rank; this one allows any packet whose finite windows generate finite-dimensional C-star algebras, replacing joint eigenspace ranks by irreducible-module multiplicity vectors — Clifford and Weyl packets included, where joint spectral projections do not exist.
artifacts:
  - research/artifacts/locally-finite-dimensional-compression-2026-09-07.md
  - notes/COMPRESSION_COLLAPSE_MF_RADICAL.md
  - notes/FALSE_KAZHDAN_COMPRESSION_INDEX_TO_PHASE.md
---

Let W be countable, let pi be a norm-corona representation, let
Lambda <= W have property (T), and let s Lambda s^-1 <= Lambda.
Suppose pi(k) has finite order, every finite window of its Lambda
conjugacy orbit generates a finite-dimensional C-star algebra, and
pi(k) commutes with pi(s Lambda s^-1). Then pi(k) commutes with
pi(Lambda).

The route semisimple-packet-multiplicity-collapse-proof proves this
statement for growing finite-dimensional orbit algebras. In fact its
theorem applies to an arbitrary element of the corona: finite order
and unitarity are unnecessary.

## Why growing windows work

Lift each fixed finite-dimensional algebra on a tail, then diagonalize
to homomorphic lifts on growing algebras. For each fixed pair h,g,
average the conjugating unitary over C*(1,a,a_g) and take its polar
part. This gives exact covariance of the displacement c_n(g)=a_g-a
under a unitary W_n(h,g) with ||W_n(h,g)-V_n(h)|| -> 0.

Normalize by the maximum Hilbert--Schmidt displacement k_n over a
finite symmetric generating set. Exact local covariance gives the
word bound ||c_n(g)||_HS <= |g| k_n, and the corrected unitary gives

    ||c_n(hg)-c_n(h)-Ad(V_n(h))c_n(g)||_HS / k_n
        <= 2 ||W_n(h,g)-V_n(h)|| |g| -> 0.

Thus the weighted Hilbert ultraproduct carries a nonzero cocycle
vanishing on the compressed subgroup. Property (T) makes it a
coboundary, while the Kazhdan projection identity in the finite
adjoint corona identifies the two fixed spaces and forces it to vanish.

Only convergence for each fixed pair is used. The corrections need
not satisfy a multiplication law, and the dimensions of the orbit
algebras may grow without a uniform bound.

The fixed finite-packet theorem and commuting torsion collapse are
special cases. Applying this theorem to the locally finite Jacobson
ideal also proves the head-root endpoint through
binary-jacobson-mf-collapse-proof.

## Proof status

The artifact contains a complete written proof and its scope audit.
The new growing-window analytic assembly has not been formalized in
Lean; existing fixed-packet and transport certificates are not
certificates of this extension. Exact finite-dimensionality of each
orbit window remains a hypothesis.
