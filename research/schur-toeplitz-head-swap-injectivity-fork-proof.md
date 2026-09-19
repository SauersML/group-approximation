---
rg: 2
id: schur-toeplitz-head-swap-injectivity-fork-proof
kind: route
title: Correct the odd head swap and isolate the faithful Steinberg HNN fork
target: schur-toeplitz-head-swap-exposes-the-steinberg-injectivity-fork
requires:
  - schur-idempotent-is-an-injective-toeplitz-defect
  - schur-toeplitz-envelope-has-proper-self-embedding
  - atlas-steinberg-context-absorption
  - tail-wordized-child-surplus-collision-supplies-rct7
---

Put `P=1-xy`, `e_1=xPy`, `a=xP`, and `b=Py`.  The Toeplitz relations give

```text
P^2=P,       Px=0,       yP=0,
ab=e_1,      ba=P,       a^2=b^2=0.
```

The four elements are the matrix units of the first two head coordinates.
In particular `c=1-P-e_1` is an idempotent orthogonal to their two-by-two
corner, while `(a+b)^2=P+e_1`.  Therefore

```text
s=c+a+b=1-P-e_1+a+b
```

satisfies `s^2=1` and `s e_1 s=P`.  This proves the odd-characteristic sign
correction.  Direct matrix-unit multiplication also gives

```text
a=e_1 s P,                         b=P s e_1.           (1)
```

The established self-embedding has

```text
sigma(P)=e_1,
sigma(x)=x^2y+P,                   sigma(y)=xy^2+P.
```

Since `x=x^2y+a` and `y=xy^2+b`, equation `(1)` recovers `x` and `y` from
`sigma(R_f)`, `k[B_f]`, and `s`.  Hence

```text
R_f=<sigma(R_f),k[B_f],s>.
```

The packet algebra and field are finite.  Steinberg additivity and the
relation `[x_ij(r),x_jk(t)]=x_ik(rt)`, with spare indices, therefore turn this
ring generation into a fixed finite root-word head menu.

The ring `R_f` is finitely presented.  The rank-five Krstic--McCool theorem,
pinned in `atlas-steinberg-context-absorption`, makes `St_5(R_f)` finitely
presented.  Injectivity of `sigma` entrywise makes the induced endomorphism of
`EL_5(R_f)` injective.  It does not imply injectivity on the Steinberg cover:
the kernel of `St_5(sigma)`, if nontrivial, lies in the Steinberg `K_2` kernel,
and coefficient inclusions are not left-exact there without an additional
argument.

The apparent compression is not that argument.  The additive map
`rho(r)=yrx` is inverse to `sigma` on `sigma(R_f)`, but on the full ring

```text
rho(r)rho(t)=yr(1-P)tx
```

need not equal `rho(rt)`.  Already

```text
rho(x)rho(y)=xy=1-P,                 rho(xy)=y(xy)x=1.
```

Thus `rho` is not a ring retraction and functoriality gives no left inverse
to `St_5(sigma)`.

Because `St_5(R_f)` is finitely presented and the images of its finite
generators are finite words, the formal ascending-HNN presentation has a
finite list of generators and relators even if `St_5(sigma)` is not
injective.  What injectivity supplies is Britton embedding of the base, and
hence survival of the marked Schur word in the exact completeness model.  On
the elementary side the coefficient shift is faithful, but only the
established recursively presented model is available.  This is precisely the
finite-presentation/faithful-base fork asserted by the target.

Finally, for `e_n=sigma^n(P)` the element `u_n=1-2e_n` is an involutive unit.
The standard six-root torus word

```text
h_ij(u_n)=w_ij(u_n)w_ij(-1)
```

maps to `diag(u_n,u_n^(-1))=diag(u_n,u_n)` in the elementary quotient.  Thus
odd characteristic and conversion of the raw defect into a reflection are
not obstructions.  The established scalar collision route uses instead the
aggregate corrected-child reflection.  No identity in the prerequisites
identifies that projection with `e_n`, so corrected-child wordization remains
open independently of Steinberg shift injectivity.

This route establishes the audit and its strict fork only.  It proves neither
`ker(St_5(sigma))=1` nor the corrected-child coefficient identity.
