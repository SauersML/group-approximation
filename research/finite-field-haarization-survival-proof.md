---
rg: 2
id: finite-field-haarization-survival-proof
kind: route
title: Track the two crossed-product inclusions and push affine Haar through the recovery map
target: finite-field-haarization-survival-dichotomy
requires:
  - affine-haar-process-fourier-modulus-compiler
  - finite-field-convolution-haarizes-affine-support
---

For `(HSD1)`, the pullback `f |-> f after pi` is a unital normal
trace-preserving `Lambda`-equivariant embedding of the base probability
algebras.  Together with the common canonical unitaries it integrates to the
trace-preserving crossed-product embedding `(HSD2)`.  Non-CE passes upward
from a tracial subalgebra.  The affine homogenization theorem then places its
target as a positive central corner of a Haar algebraic crossed product, so a
non-CE source makes the ambient semidirect-product group non-hyperlinear.

For the linear-retention assertion, write the assumed affine Haar law as
`m_(w_0+Q)` on a closed subgroup coset of `W`.  A continuous affine map sends
Haar measure on a compact-group coset to Haar measure on the image coset:
translation handles `w_0`, and the continuous homomorphism part pushes Haar
on `Q` to Haar on its compact image.  Consequently

```text
R_* L_*(nu x m_V)
```

is affine Haar.  By `(HSD3)` this measure equals `nu`.  The Fourier modulus
criterion proves the claimed impossibility whenever the source was not
already affine Haar.

For the erasure check, translation invariance of full Haar gives, for every
Borel set `B subset E`,

```text
Pr[Z+U in B]=integral m_E(B-z) dnu(z)=m_E(B).
```

Finally `Sigma` and each coordinate projection are equivariant
measure-preserving maps from the product action to their respective factor
actions.  Pullback reverses those arrows and yields the two crossed-product
subalgebras described in `(HSD4)`.  There is no inclusion between them in
general, proving the direction/no-permanence statement without making any
unsupported claim that non-CE descends to factors.
