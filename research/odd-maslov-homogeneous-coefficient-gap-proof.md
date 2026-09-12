---
rg: 2
id: odd-maslov-homogeneous-coefficient-gap-proof
kind: route
title: Compactify projective positive-definite coefficients and expose a forbidden finite projective summand
target: odd-maslov-homogeneous-coefficients-have-a-fixed-size-defect-gap
requires:
  - deligne-triple-cover-fd-central-invisibility
  - finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres
---

The twisted Fourier-multiplier criterion says that `(OHG4)` is ucp exactly
when `C` is normalized positive definite for the difference multiplier
`delta`.  Equivalently, there are a `delta`-projective unitary representation
`pi` on a Hilbert space `K` and an isometry

```text
V:C^n -> K
```

such that

```text
C_g=V^* pi(g)V.                                         (OHP1)
```

In particular every `C_g` is a contraction, so every summand in `(OHG3)`
is nonnegative.

For fixed `n`, the set of normalized `M_n`-valued `delta`-positive-definite
functions is compact in the topology of pointwise matrix convergence: it is
a closed subset of the product of the matrix unit balls.  The left side of
`(OHG3)` is a continuous nonnegative function on this compact set, hence has
a minimum.

If that minimum were zero, every generator coefficient would satisfy

```text
C_s^*C_s=C_sC_s^*=I_n.                                  (OHP2)
```

Equality in the compression Schwarz inequality for `(OHP1)` then gives

```text
pi(s)V=VC_s,              pi(s)^*V=VC_s^*.              (OHP3)
```

Thus `V C^n` reduces every `pi(s)`, and hence reduces `pi(Gamma)`.  The
matrices `C_s` consequently form an `n`-dimensional `delta`-projective
unitary representation of `Gamma`.  Deligne finite-dimensional central
invisibility forbids such a representation for every odd difference class.
Therefore the compact minimum is strictly positive; call it `kappa_n`.

Finally, if `r i=id`, Schwarz gives

```text
r(I-i(u_s)^*i(u_s))=r(I-i(u_s)i(u_s)^*)=0.              (OHP4)
```

Using `(OHG4)`, these are precisely the coefficient defects appearing in
`(OHG3)`, tensored with the even-fibre identity.  This proves the stated
positive-kernel interpretation.
