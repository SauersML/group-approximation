---
rg: 2
id: torsion-free-small-spread-spectra-are-integer-atomic
kind: claim
title: Over a torsion-free group an integral self-adjoint matrix with spectrum in an interval of length below four has integer-atomic spectral measure
distinct_from:
  finite-spectrum-integral-elements-obey-determinant: that assumes finite spectrum and holds over every group; this derives finite spectrum with integer multiplicities from a small spectral spread, over torsion-free groups
  torsion-free-integral-zeta-is-an-integer-euler-product: that is the integrality of the trace zeta series; this is its consequence for spectra of spread below four, through Pólya's rationality theorem
---

**ESTABLISHED** by `torsion-free-small-spread-integer-atomic-proof`.

Let `G` be torsion-free and let `T in M_n(Z[G])` be self-adjoint with
`sigma(T)` contained in `[a, b]`, `b - a < 4`. Then

```text
mu_T = sum_i k_i delta_(lambda_i),   k_i in {1, 2, 3, ...},
```

so `T` has finite spectrum and every spectral projection has integer trace. By
`finite-spectrum-integral-elements-obey-determinant`, the `lambda_i` form a
Galois-stable set of totally real algebraic integers.

**Case `n = 1`.** Integer masses summing to `1` leave a single atom, so `T` is
the scalar `tau(T) in Z`. Every non-scalar self-adjoint element of `Z[G]` over a
torsion-free group therefore has spectral spread at least `4`. The bound is
sharp: for `g` of infinite order, `sigma(g + g^(-1)) = [-2, 2]`.

**Consequences for counterexamples.** Take an integral self-adjoint matrix over
a torsion-free group whose spectral measure is not integer-atomic. This covers
every Strong Atiyah failure with integral coefficients, and every determinant
violation, since those have infinite spectrum. Its spectrum, and the spectrum of
each integral polynomial image `Q(T)` that is not integer-atomic, has spread at
least `4`.

With torsion the statement fails: over `Z/2`, `T = g` has spectrum `{-1, 1}` with
masses `1/2`.
