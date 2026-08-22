---
rg: 2
id: finite-field-haarization-survival-dichotomy
kind: claim
title: Haarization preserves a non-CE source through an action factor, while every linearly recoverable masking is already affine Haar
distinct_from:
  finite-field-convolution-haarizes-affine-support: that constructs the limiting affine Haar law; this determines when the original crossed product embeds in the limit and rules out injective linear retention as a way to force that embedding.
  coinduction-preserves-but-cannot-create-algebraic-envelope: that treats change of actor and the missing finite induction corner; this treats independent products, sum factors, and affine masks with the actor fixed.
  affine-haar-process-fourier-modulus-compiler: that compiles a process which already passes the affine Fourier test; this proves that retaining a process through a linear mask cannot make it pass for the first time.
---

Let `Lambda` act by shifts on a compact finite-field coordinate group `E`,
and let `nu` be invariant.  Put `M_nu=L^infinity(E,nu) rtimes Lambda`.

There is one precise positive permanence statement for the affine-support
Haarization `A=x_0+K` of
`finite-field-convolution-haarizes-affine-support`: if there is a
`Lambda`-equivariant measure-preserving factor map

```text
pi:(A,m_A) -> (E,nu),                                  (HSD1)
```

then pullback of functions and the same actor unitaries give a trace-preserving
inclusion

```text
M_nu -> L^infinity(A,m_A) rtimes Lambda.                (HSD2)
```

Thus non-CE of `M_nu` survives, and the one-coordinate homogenization in
`affine-haar-process-fourier-modulus-compiler` produces a non-hyperlinear
semidirect product.  A nonlinear factor `(HSD1)` is therefore a sufficient
and sharply stated target.

The natural injective/difference/product constructions cannot supply it by
linear retention.  Let `V` carry Haar measure, independently of `Z~nu`, let
`L:E x V->W` be continuous affine-linear, and suppose a continuous affine
map `R:W->E` recovers the source:

```text
R(L(Z,U))=Z almost surely.                              (HSD3)
```

If `L_*(nu x m_V)` is affine Haar, then `nu` itself is affine Haar.  Indeed a
continuous affine image of affine Haar measure is affine Haar, and `(HSD3)`
identifies that image with `nu`.  Hence a source failing the modulus-binary
Fourier test cannot be made Haar while a linear decoder retains it.  This
covers invertible changes of variables, retaining both a one-time pad and its
masked label, and retaining one input together with sums/differences of
independent copies.

If the decoder is discarded, Haarization can erase everything: for an
independent full-Haar `U` on `E`, the law of `Z+U` is full Haar for every
`nu`.  So the sum law alone carries no universal copy of the source algebra.
The remaining opening is exactly a **nonlinear equivariant factor** from the
affine support hull, or a genuinely non-Cartan crossed-product embedding; no
injective affine mask bridges the gap.

At finite convolution level the direction issue is explicit.  The sum map
`Sigma:E^n->E` gives

```text
L^infinity(E,nu^(star n)) rtimes Lambda
   -> L^infinity(E^n,nu^n) rtimes Lambda,               (HSD4)
```

while a coordinate gives `M_nu` as another subalgebra of the product crossed
product.  Non-CE of the product does not descend to its sum-factor subalgebra;
`(HSD4)` points in the wrong direction for hereditary Connes embeddability.
