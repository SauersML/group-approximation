---
rg: 2
id: iwahori-parabolic-boundary-splitting-is-uniform
kind: claim
title: Interior and Eisenstein cohomology split with uniform angle for congruence local systems
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-eisenstein-angle: that proves transversality of the two vertex restriction maps after passing to the residue model; this asks that the residue and interior pieces themselves have a uniformly conditioned splitting in the original fixed-generator cochain norm.
---

For each of the three fixed modular groups `V` and every finite-dimensional
unitary congruence local system `E=Ad rho`, consider the boundary sequence
from parabolic/interior cohomology to ordinary cohomology and cusp residues.
Prove that it admits a splitting whose operator norm, measured in the fixed
cellular quotient norm, is bounded independently of `rho` and its dimension.
Equivalently, the angle between the interior and Eisenstein summands stays
uniformly positive over all congruence coefficient sectors.

This is the remaining bookkeeping not supplied by the general fixed-complex
Hodge comparison.  Near-invariant eigenvectors of a parabolic generator make
the assertion nonformal: an argument may not invert `1-Ad rho(u)` on its
orthogonal complement without a uniform spectral bound, because its nonzero
eigenvalues can approach zero in high-order congruence quotients.  A valid
proof must instead use the orbit-size weighted residue model, the two
complementary Iwahori cusp widths, or a global property-`(tau)` estimate.

## Attempts

- In the Shapiro model over a principal kernel, boundary residues are vectors
  on cusp orbits and the fixed-generator cochain norm is a deck-invariant
  cellular norm.  The desired statement becomes a uniform singular-value
  bound for the finite incidence map from cusp residues to cellular
  cohomology, after quotienting constants.
- `iwahori-eisenstein-angle-proof` shows that the **two-vertex mismatch** on
  residue vectors has exact singular interval `[1,3]`.  This does not by
  itself bound the lift of one residue vector back to a vertex cocycle; the
  lift/splitting map is the missing operator here.
- A proof by orthogonal projection in an arbitrary cochain inner product is
  insufficient unless restriction preserves that orthogonal decomposition
  with uniform norm.  This is exactly the cancellation that must be excluded
  when the cuspidal and Eisenstein lower bounds are assembled.
