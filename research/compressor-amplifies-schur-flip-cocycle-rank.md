---
rg: 2
id: compressor-amplifies-schur-flip-cocycle-rank
kind: claim
title: A finite compressor recurrence amplifies Schur flip squares to supercritical cocycle rank
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  compressor-returns-schur-child-masas: that asks for a returned positive-density child module; this is the equivalent projective-holonomy formulation using the explicit flip automorphisms of the packet.
  projective-holonomy-rank-forces-exponential-multiplicity: that computes the exact multiplicity cost once a rank-`2r` cocycle is active; this must create that rank self-similarly with uniform normalized-HS control.
  same-model-supercritical-clifford-trigger: that allows an arbitrary computational Clifford challenge after detecting the model size; this restricts the challenge to iterated copies of the explicit two-flip Schur packet cell.
---

Construct a finite one-sided-compressor presentation which recursively
addresses independent conjugates of the flip square `(SPF4)` and has the
following finite-dimensional microstate property.

On every positive-density forbidden packet carrier of external multiplicity
`m`, either named relator energy is bounded below by a universal constant, or
the returned stable-letter actions contain a binary projective commutator
form of rank `2r` with

```text
r>log_2 m.                                                        (SFA1)
```

All packet exactification, address transport, commutation checks, and return
errors must be bounded by a constant multiple of the original normalized-HS
relator energy, independent of `m`, `r`, and recursion depth.  In the exact
non-CE tracial representation, the recurrence must be realizable on diffuse
multiplicity modules, so it does not destroy completeness.

By `projective-holonomy-rank-forces-exponential-multiplicity`, the low-energy
branch of `(SFA1)` would force `2^r|m`, impossible.  The claim would therefore
give the desired dimension-free return charge.

## Attempts

- Repeating a fixed finite number of flip squares only gives a fixed divisor
  and is HS-dilutable.
- Addressing conjugates by ordinary long words accumulates error with depth
  and reproduces only a large finite hyperlinear profile.
- The active route is a PCP/compressor recurrence: a local inconsistency must
  either pay immediately or copy the flip cell into enough independent
  returned directions that cocycle rank outruns the current multiplicity.
- `schur-flip-wreath-compressor-has-infinite-cocycle-rank` removes recursion
  depth on the completeness side: one strict Kun--Thom compressor already
  gains infinitely many independent flip sites.  The live route
  `schur-flip-amplification-from-wreath-site-recovery` leaves the concrete
  matrix-coordinate statement
  `matrix-recovery-of-schur-flip-wreath-sites`.
- Infinite index and fixed-window recovery alone are explicitly refuted by
  `infinite-index-does-not-force-supercritical-site-rank`.  The remaining
  coordinate statement must contain a dimension-diagonal trigger reacting to
  residual spectator multiplicity, not merely a better compactness estimate.
