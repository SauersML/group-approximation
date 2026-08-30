# Audit: finite-dimensional Følner carriers in the augmentation ideal

Date: 2026-08-30

## Construction

For finite `F<=K`, the complement of the averaging projection

```text
e_F=1-|F|^(-1)sum_(g in F)lambda_g
```

lies in the augmentation ideal and is exactly the identity on
`I intersection C*(F)`.  Average the projections `alpha^j(e_F)` over a long
integer interval.  Local finiteness puts the whole finite window in one
finite group algebra, while the Følner boundary gives
`||alpha(h)-h||<=1/N`.

Choosing `F` to contain all inverse translates of the prescribed finite
supports makes every summand act exactly as the identity on those
coefficients.  A diagonal sequence is therefore simultaneously a
coefficient approximate unit, asymptotically invariant, and quasicentral in
the crossed product.

## Support check

Each carrier has finite spectrum.  Its support projection lies in the same
finite-dimensional group algebra and in the augmentation ideal.  The
carrier is invertible on that support, so its hereditary crossed-product
subalgebra is exactly the support corner.  This converts a uniform bound on
the carrier corners into a bound on the entire augmentation-ideal crossed
product by local approximation.

## Exact seam

Finite spectrum is not a uniform gap statement.  Følner averages can acquire
arbitrarily small positive eigenvalues, and taking the support projection can
turn an `O(1/N)` covariance error into norm-one projection error.  No
invariant finite-dimensional stage, finite Rokhlin dimension, or nuclear-
dimension bound is inferred.  The remaining target is a uniform analysis of
the corners `s(I rtimes Z)s`, or a method that uses the positive carriers
without cutting at zero.
