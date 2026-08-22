---
rg: 2
id: three-root-asymmetric-finite-core-pushout-proof
kind: route
title: Localize the coefficients to GL3(F2) and apply hyperlinear coefficient injectivity
target: three-root-asymmetric-kl-word-has-finite-core-pushout
requires:
  - kervaire-laudenbach-holds-for-hyperlinear
  - leavitt-gl-equals-el-and-perfect-unit-group
  - full-leavitt-idempotent-defect-saturation
---

The three elementary matrices lie in the upper-left constant
`GL_3(F_2)` block of `EL_20(R)`.  They generate every elementary root:

```text
[x_12(1),x_23(1)]=x_13(1),
[x_23(1),x_31(1)]=x_21(1),
[x_31(1),x_12(1)]=x_32(1).
```

Thus they generate `EL_3(F_2)=GL_3(F_2)` (the determinant is automatically
one over `F_2`); the standard order formula gives

```text
|GL_3(F_2)|=(2^3-1)(2^3-2)(2^3-2^2)=168.
```

Every nonzero elementary root normally generates `EL_20(R)` by the
machine-checked theorem `HilbertHotel.normalClosure_elementaryRoot_eq_top`,
so each coefficient is individually a normal generator of `G` after rank
transport.  This strength will not be used to infer the false conclusion
that the equation kills it.

Moving each coefficient past the accumulated power of `t` gives `(TAK2)`:
the prefix exponents before `r,s,v` are respectively `0,1,2`, while the final
exponent is `1`.  Thus the first Fox/exponent test is passed exactly and
`w` is a generator of `N_1^ab`.

The artifact independently enumerates all invertible three-by-three binary
matrices and multiplies the six factors in `(TAK1)`; no matrix solves the
equation.  This internal failure is not coefficient collapse.  Finite `H` is
hyperlinear, and `kervaire-laudenbach-holds-for-hyperlinear` implies that the
canonical map

```text
H -> P_H=(H*<t>)/<<w>>
```

is injective because `deg_t(w)=1`.

Finally, free products and quotients are pushouts.  Since all coefficients of
`w` lie in `H<=G`,

```text
G*<t> = G *_H (H*<t>),
P_G    = G *_H P_H.
```

Now both edge maps are injective, so this is an amalgamated free product in
the Bass--Serre sense.  Its normal-form theorem injects the `G` vertex group,
proving `(TAK3)` and showing `<<w>>` is proper.
