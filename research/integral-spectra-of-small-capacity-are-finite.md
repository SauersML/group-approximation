---
rg: 2
id: integral-spectra-of-small-capacity-are-finite
kind: claim
title: Over every group an integral self-adjoint matrix whose spectrum has capacity below one has finite spectrum
distinct_from:
  torsion-free-small-spread-spectra-are-integer-atomic: that assumes a torsion-free group and a spectral interval of length below four, and gets integer masses through the zeta Euler product; this holds over every group and every spectral set of capacity below one, disconnected sets included, and gets finite spectrum from the Stieltjes transform alone, with no claim about the masses.
  finite-spectrum-integral-elements-obey-determinant: that assumes finite spectrum and derives rational, Galois-equal masses; this derives finite spectrum from a capacity bound.
---

**ESTABLISHED** by `integral-small-capacity-finite-spectrum-proof`.

Let `G` be any countable group and `T in M_n(Z[i][G])` self-adjoint, acting on
`l^2(G)^n`, with `sigma = sigma(T)` its spectrum in `M_n(C*_r(G))`. If the
logarithmic capacity of `sigma` is below `1`, then `sigma` is finite. Hence:

- `T` satisfies `m(T) = 0` for a monic squarefree `m in Z[x]`, and every
  spectral projection `chi_({lambda})(T)` is a polynomial in `T` with
  coefficients in `Q(lambda)`, so it lies in `M_n(Qbar[G])`;
- by `finite-spectrum-integral-elements-obey-determinant` (for entries in
  `Z[G]`; entries in `Z[i][G]` pass through the real `2n x 2n` form), the
  masses are rational and Galois-conjugate atoms carry equal mass.

**Capacity of typical spectral sets.** A segment of length `l` has capacity
`l/4`. The symmetric two-interval set `[-b,-a] ⊔ [a,b]` has capacity
`sqrt(b^2 - a^2)/2`, by pushing forward under `x -> x^2`. So a gapped spectrum
can have capacity below one while its spread is far above four.

**The masses need not be integers**, even over torsion-free groups, once the
spectrum is disconnected. The measure `(delta_2 + delta_(-2))/2` has capacity
`0`, integer moments, and integer zeta coefficients
`exp(sum m_j z^j/j) = (1 - 4z^2)^(-1/2) in Z[[z]]`. So it passes every
arithmetic test in `torsion-free-integral-zeta-is-an-integer-euler-product`.
The integer masses of the connected case come from the single-valuedness of
`exp(-integral log(w-x) d mu)` around the whole interval, which fails around a
component of non-integer mass.
