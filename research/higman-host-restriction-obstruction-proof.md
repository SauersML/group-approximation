---
rg: 2
id: higman-host-restriction-obstruction-proof
kind: route
title: Combine relative-area telescoping with regularized LEF partial models
target: higman-host-restriction-stops-at-separating-partial-models
requires:
  - subgroup-dehn-function-is-the-hyperlinearity-modulus
  - ffgs-local-hs-examples-resist-split-finite-presentation-wrappers
---

Apply `subgroup-dehn-function-is-the-hyperlinearity-modulus` to the embedded
source generators.  This gives `(FHD1)` and, after diagonalizing the source
radius against the host defect, no more than an approximate representation
of `H`.

The Fibonacci source `H` is LEF by FFGS Theorem 5.4.  Local embeddings of
increasing balls into finite groups are partial homomorphisms.  Passing to
the left regular permutation representation makes every retained nonidentity
element have trace zero, hence normalized-HS distance `sqrt(2)` from the
identity.  These are already locally exact, proving sharpness of the partial
rounding conclusion.

If a multiplicative presentation return from the host to `H` fixed the
embedded source generators, it would descend to a group retraction.  The
retract obstruction in the second required claim excludes this.  Word-metric
distortion and nonmultiplicative coarse retractions do not alter either
argument.

