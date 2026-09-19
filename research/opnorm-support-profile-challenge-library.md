---
rg: 2
id: opnorm-support-profile-challenge-library
kind: claim
title: Build an authenticated operator-norm challenge for every marked support profile
distinct_from:
  finite-predicate-signed-permutation-sector: that realizes one finite Boolean predicate inside an exact irreducible finite-group sector; this must authenticate that sector by ordinary group words and challenge every finite-dimensional support profile carrying it.
  multiplicity-pi-turing-tape: that reads unbounded exact multiplicity using polynomial identities; this uses only the finite zero-versus-positive support profile and no dimension oracle.
  bcs-to-lcs-exact-support-gap: that seeks a positive normalized-HS mass gap for a tracial BCS; this needs only a worst-direction operator-norm violation on one nonzero sector.
  finite-static-nemesis-core-needs-canonical-base-embedding: that is a canonical-trace finite-subcover criterion; this asks for word-authenticated operator-norm challenges and an infinite-dimensional marked completion.
---

**OPEN.**  Construct, uniformly from a machine instruction and the fixed
signed-permutation CPU, ordinary group-word gadgets with the following
properties.

1. Every sufficiently accurate finite-dimensional model exactifies on the
   CPU and exposes one of the finitely many support profiles from
   `finite-group-opnorm-support-profile`.
2. Whether the fixed marked carrier is present is authenticated by group
   words, not by an unavailable group-algebra central idempotent.
3. For every profile carrying the mark, a computably emitted finite challenge
   either removes that profile or forces a definite operator-norm relator
   violation, independent of ambient matrix dimension.
4. The compatible challenge stream has one exact infinite-dimensional group
   representation in which the marked word remains nontrivial.

The fourth clause prevents the challenge library from merely proving the
mark trivial in the presented group.  The open content is word-level sector
authentication, cross-context consistency, and infinite-dimensional
satisfiability; finite-predicate realization and finite-group correction are
already separate established inputs.

## Attempts

- **Central character projector.**  After exactification, the standard
  group-algebra idempotent detects an irreducible sector perfectly, but it is
  an additive linear combination rather than a group word.  No current gadget
  turns its zero-versus-nonzero support into the required ordinary word
  semantics without also constraining the intended infinite model.
- **Candidate-specific nemesis.**  Appending a relation after inspecting one
  matrix defeats only a model of the old prefix; it does not make that matrix
  approximate the post-challenge group.  The challenge library must be
  precompiled into the final relator stream.
- **Raw polynomial identity detector.**  Amitsur--Levitzki can read a matrix
  dimension in an associative algebra, but no robust multiplicative
  group-word translation is known here.  This lane deliberately avoids that
  dimension-oracle interface and attacks only finitely many support types.
