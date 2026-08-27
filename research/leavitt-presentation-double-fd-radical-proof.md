---
rg: 2
id: leavitt-presentation-double-fd-radical-proof
kind: route
title: Restrict to the two vertices, apply rigidity, and use residual finiteness of the free fold
target: leavitt-presentation-double-fd-radical-is-fold-kernel
requires:
  - simple-map-quotient-has-rigid-fd-restriction
  - virtually-free-full-algebras-are-rfd
---

Let `i_0,i_1:F->P=F *_K F` be the vertex maps and let `p:P->F` be the fold.
For an exact finite-dimensional unitary representation `pi:P->U(d)`, set

```text
u=pi i_0,                     v=pi i_1.
```

The amalgam relation says `u(k)=v(k)` for every `k in K`.  Since `F/K` is
infinite, finitely generated, simple and nonsofic,
`simple-map-quotient-has-rigid-fd-restriction` gives `u=v`.  The universal
property of the amalgam now gives a representation `sigma:F->U(d)` with

```text
pi=sigma p.                                                   (PFR3)
```

Thus `ker(p)<=ker(pi)` for every finite-dimensional `pi`.

For the reverse inclusion, take `w notin ker(p)`.  Then `p(w)!=1` in the
finitely generated free group `F`.  Residual finiteness supplies a finite
quotient `a:F->A` with `a(p(w))!=1`.  Composing `a p` with the left regular
permutation representation of `A` gives a finite-dimensional unitary
representation of `P` which does not kill `w`.  Hence the intersection of
the finite-dimensional kernels is contained in `ker(p)`, proving `(PFR1)`.

Every unital finite-dimensional star representation of `C*(P)` is the
integrated form of a finite-dimensional unitary representation of `P`, so
the factorization `(PFR3)` shows

```text
ker(C*(p)) <= intersection_(Phi:C*(P)->M_d) ker(Phi).
```

Conversely, if `a notin ker(C*(p))`, then `C*(p)(a)` is nonzero in `C*(F)`.
The established RFD theorem for finitely generated virtually free groups
applies to the free group `F` and gives a finite-dimensional star
representation `theta` of `C*(F)` with
`theta(C*(p)(a))!=0`.  Hence `theta C*(p)` detects `a`, proving `(PFR1*)`.

If `tau_j` are normalized characters of exact finite-dimensional
representations, `(PFR3)` gives `tau_j((u_w-1)^*(u_w-1))=0` for every
`w in ker(p)`.  Convex combinations and pointwise limits preserve this
identity, proving `(PFR2)`.

Finally, for `f_0 notin K`, the word
`i_0(f_0)i_1(f_0)^(-1)` is reduced and nontrivial by the normal-form theorem
for amalgamated free products, while its fold is the identity.  This gives
the explicit nontrivial radical element used in the claim.
