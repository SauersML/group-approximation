# STW LXXXVII: property-A ghost-packet firewall audit (2026-08-30)

## Result

For a bounded-geometry property-A space, Roe--Willett identify the ghost
ideal of the uniform Roe algebra with the compact operators.  Every finite
packet in that ideal can therefore be approximated, to arbitrary norm
accuracy, by compression into one finite coordinate corner.  Compression is
c.p.c. and the return inclusion is a star-homomorphism, so this is a genuine
zero-colour approximation with no diagonal-bimodularity hypothesis.

## Checks

- Finite coordinate projections converge strongly to the identity.  Their
  two-sided compressions converge in norm on each compact operator, and a
  single projection works for a finite packet.
- The finite corner is the full matrix algebra: every matrix unit supported
  on the finite coordinate set has finite propagation and lies in the
  uniform Roe algebra.
- The return map is a possibly nonunital star-homomorphism into the ambient
  algebra, which is c.p.c. order zero exactly as nuclear dimension requires.
- The theorem handles arbitrary admissible c.p.c. order-zero approximation
  schemes by explicitly exhibiting one such scheme; it does not assume a
  Schur, diagonal, boundary, or limit-operator form.
- Because property-A ghosts are compact, their corona classes vanish.

## Boundary

This is a precise impossibility reduction, not a lower bound.  It rules out
finite-packet arguments supported entirely in the ghost ideal, even when the
space has infinite asymptotic dimension.  It does not rule out mixed packets
containing non-ghost operators, obstructions to simultaneous approximation
across an unbounded family of packets, or invariants carried by non-ghost
boundary/limit operators.

## Independent audit

An independent adversarial audit checked the exact Roe--Willett scope,
two-sided compact compression, the full finite corner, complete positivity,
the nonunital order-zero return map, and the corona statement. The package
passed without a mathematical or scope defect.
