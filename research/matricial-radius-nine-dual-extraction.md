---
rg: 2
id: matricial-radius-nine-dual-extraction
kind: claim
title: A dimension-sensitive hierarchy extracts a rational radius-nine atlas separator
distinct_from:
  atlas-radius-nine-trace-separator: that is the mathematical inequality; this asks for a finite, replayable dual proof in a specified matricial positivity calculus.
  tracial-npa-cannot-separate-canonical-trace: that excludes the standard tracial hierarchy; this requires matrix-specific identities or exterior-power and invariant-theory certificates unavailable in arbitrary tracial von Neumann algebras.
artifacts:
  - research/artifacts/trace-promotion-renormalization-program-2026-08-20.md
---

Construct a nested computational hierarchy over the radius-nine atlas trace
word orbit basis whose dual certificates are:

1. rational and exactly replayable;
2. sound in every matrix size after adding the fixed atlas relator-energy
   penalty; and
3. not sound in arbitrary tracial von Neumann algebras, because the proof
   explicitly uses finite-dimensional invariant theory, exterior powers, or a
   dimension-indexed argument subsequently made uniform in `n`.

At some finite level the dual optimum supplies coefficients `a_w,C,c` with
the signs required by `atlas-radius-nine-trace-separator`.  Direct finite-size
matrix optimization may seed the candidate, but is not the certificate.

The campaign has a hard stopping rule in both directions: a replayed rational
dual closes the claim; a canonical-trace-feasible dual reveals that the
implementation has accidentally reverted to the forbidden tracial NPA cone.

## Attempts

- Enumerate cyclic radius-nine word orbits and use finite-size unitary
  optimization only to guess a sparse coefficient vector.
- Rationally reconstruct it, then seek a uniform proof from Procesi trace
  identities, exterior powers, and Schur-complement inequalities.
- Standard tracial moment matrices are excluded. If canonical atlas moments
  remain feasible in the implemented cone, that run is diagnostic only.
- **Closed-body duality removes rational reconstruction as a separate hole.**
  `radius-nine-separator-is-closed-matricial-moment-gap` proves that the union
  over all matrix sizes, after adjoining the single relator-energy coordinate
  and taking closure, is a compact convex body.  The requested rational dual
  exists if and only if the canonical radius-nine point lies outside this
  body; strict separation can always be rationalized while keeping a positive
  defect coefficient.  Hence a finite-size SDP is useful only if accompanied
  by a rigorous all-size outer bound on that body.  Sampling or a dimension
  cap alone separates from an inner approximation and is not a certificate.
- **Bounded-degree matrix identities do not provide the missing outer bound.**
  `radius-nine-pi-exterior-all-size-fence` uses
  the minimal PI degree and spectator amplification.  At radius nine the
  standard-identity cases stop at dimension four, while `M_5(C)` has no
  nonzero PI of degree at most nine; amplification preserves every normalized
  moment and defect while making the dimension arbitrary.  Hence an
  Amitsur--Levitzki/exterior-power case split cannot close this claim.  The
  remaining target is a universal matrix trace inequality, not an identity.
- **Fixed packet Gram/SOS proofs are dimension-free as well.**
  `atlas-radius-nine-packet-gram-sos-is-tracial` shows that finite A4 packet
  Reynolds averages, operator-valued Gram positivity, fixed matrix
  compressions, and ordinary (regularized) Schur complements all make sense
  with the same constants in every finite tracial von Neumann algebra.  Their
  SOS consequences therefore hold in the regular representation and cannot
  be negative at the canonical point.  The required outer bound must expose
  a genuinely matricial rank or multiplicity operation; packet symmetry and
  PSD Gram forms alone merely rebuild a richer tracial relaxation.
- **Fixed packet rank arithmetic also washes out under amplification.**
  `atlas-fixed-packet-arithmetic-has-no-hs-gap` proves that every finite
  homogeneous congruence or divisibility condition on the A4 multiplicity
  lattice is killed exactly by multiplying all multiplicities by the exponent
  of its finite residue group.  More generally, normalized points of a fixed
  finitely generated multiplicity semigroup are dense in the projectivized
  real cone.  Even the quadratic commutant-rank density is continuous on this
  simplex.  Therefore a positive gap from fixed packet ranks is already a
  real representation-type incompatibility; it is not matrix-only
  integrality.  The remaining branch must be dimension-activated or use data
  outside the fixed type profile.
