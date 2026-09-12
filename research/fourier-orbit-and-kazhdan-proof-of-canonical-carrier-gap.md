---
rg: 2
id: fourier-orbit-and-kazhdan-proof-of-canonical-carrier-gap
kind: route
title: Kill nonconstant Fourier coefficients on infinite conjugacy orbits and apply the Kazhdan gap
target: infinite-conjugacy-orbits-give-canonical-carrier-no-capture
requires:
  - embedded-group-algebra-carriers-have-no-excess-fixed-component
---

Identify `L^2(L(G))` with `ell^2(G)`. An `H`-conjugation-invariant square
summable function is constant on every `H`-conjugacy orbit and therefore
vanishes on every infinite orbit. The Fourier support of `x-c_0I` lies on
the assumed infinite orbits, proving `(ICG1)--(ICG2)`. For a spectral
projection `p`, its Fourier expansion in `L^2(L(<w>))` has constant
coefficient `beta`; the same orbit argument proves `(ICG3)`.

Now apply `embedded-group-algebra-carriers-have-no-excess-fixed-component`.
It says the fixed projection of the embedded carrier is exactly the embedded
canonical fixed projection, even if the ambient relative commutant is larger.
The property-`(T)` Poincare inequality for the conjugation representation on
`L^2(M)` then gives `(ICG4)`.

For canonical matrix microstates, continuous functional calculus transfers
the polynomial case directly. In the spectral-projection case choose `E`
with Haar-null boundary; polynomial approximation to its indicator in the
limiting Haar spectral measure gives the same lower bound up to `o(1)`.
