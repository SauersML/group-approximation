---
rg: 2
id: core-expectation-zero-mode-proof
kind: route
title: Amplify the mod-three pair outside the core commutant
target: core-expectation-misses-exact-endpoint-zero-modes
requires:
  - p3-exact-iwahori-endpoints-refute-arbitrary-baseline-alignment
  - congruence-endpoint-orbits-are-restriction-ring-fibers
  - bs14-periodic-koopman-modes-refute-skeleton-regularity
---

Conditional expectation onto a finite-dimensional von Neumann subalgebra
is the Hilbert--Schmidt orthogonal projection.  Since `[c,T]!=0`, one has
`c notin beta(K)'`, hence `(CEM2)`.  Tensoring every matrix with an identity
preserves normalized Hilbert--Schmidt distance from the amplified
commutant, while all endpoint relators remain exact.  This refutes `(CEM3)`.

The slow-mode assertion for the `R`-commutant is the cyclic Fourier mode in
`bs14-periodic-koopman-modes-refute-skeleton-regularity`.  The description
of the actual zero set as a union indexed by nonnegative restriction fibers
is `congruence-endpoint-orbits-are-restriction-ring-fibers`.

