---
rg: 2
id: exact-passive-jacobian-reynolds-proof
kind: route
title: Differentiate the two order-three residuals without merging their input shifts
target: exact-passive-jacobian-is-two-reynolds-expectations
requires: []
---

Let `h` lie in the genuine real tangent space

```text
h^*=-h,             [h,R]=0,             XhX=-h,
```

and let `X_h(t)=X exp(th)`.  Set

```text
A=XS^2,  B=XRS,  k_1=Ad_(S^(-2))(h),  k_2=Ad_(S^(-1))(h).
```

Moving the exponential past `S^2`, and past `R` and then `S`, gives the
exact identities

```text
X_h(t)S^2=A exp(tk_1),       X_h(t)RS=B exp(tk_2).       (1)
```

For any `U^3=1`, differentiating `(U exp(tk))^3` at zero and
right-trivializing at `U^3=1` gives

```text
k+Ad_U(k)+Ad_U^2(k)=3 E_U(k),                            (2)
```

where `E_U=(I+Ad_U+Ad_U^2)/3` is the trace-preserving conditional
expectation onto `{U}'`.  Applying `(2)` to the two identities in `(1)`
shows

```text
DF_X(h)=3(E_A k_1,E_B k_2).                              (3)
```

The two distinct input shifts in `(3)` cannot be absorbed by separate
changes of the one common tangent variable.  Instead conjugate the two
**output** rows by `S^2` and `S`, respectively.  Then

```text
(Ad_(S^2) direct_sum Ad_S) DF_X(h)
 =3(E_(S^2 A S^(-2))h,E_(S B S^(-1))h)
 =3(E_(S^2 X)h,E_(S X R)h).                             (4)
```

Both reversed words in `(4)` have order three because they are conjugate
to `A` and `B`.  The output map is a complete isometry for the two-row
maximum norm and a unitary for the Hilbert direct-sum norm.  It therefore
preserves the kernel and all Moore--Penrose/gauge-normal inverse norms
without changing the constrained tangent domain.  Each `E_U` is completely
contractive, so the column has a universal cb bound.

Here the cb statement means the complex-linear extension from the real
tangent to

```text
{h:[h,R]=0, XhX=-h}.
```

This complex space is star closed.  For every `z` in it,

```text
h_1=(z-z^*)/2,       h_2=(z+z^*)/(2i),       z=h_1+i h_2,
```

and both `h_1,h_2` lie in the genuine skew-adjoint real tangent.  It is
therefore exactly the concrete complex span to which `(3)--(4)` extend
complex-linearly.

The only unresolved issue is the uniform cb norm of the gauge-normal
inverse of the actual shifted column `(3)` (equivalently `(4)`) on its
range.
