---
rg: 2
id: separable-exact-nowhere-scattered-tensor-permanence-proof
kind: route
title: Split an elementary tensor subquotient into simple factor ideals
target: separable-exact-nowhere-scattered-tensor-permanence
requires:
  - blanchard-kirchberg-exact-primitive-tensor-product
  - type-i-minimal-tensor-reflects-to-factors
---

Put `D=A tensor_min B` and suppose that `D` is not nowhere scattered.  The
irreducible-GCR characterization of nowhere scatteredness supplies an
irreducible representation

```text
pi:D -> B(H)
```

whose image contains `K(H)`.  Let `P=ker(pi)`.  By the
Blanchard--Kirchberg homeomorphism there are `p in Prim(A)` and
`q in Prim(B)` such that

```text
D/P isomorphic A_0 tensor_min B_0,
A_0=A/p,       B_0=B/q.                              (E1)
```

We identify the algebra in (E1) with its faithful irreducible image and put
`K=K(H)`.  The open subset of `Prim(D/P)` associated to the ideal `K` is the
singleton `{0}`.  Indeed, every irreducible representation nonzero on `K`
restricts nondegenerately to `K`.  Such a representation of `K(H)` is an
amplification of the identity representation, and its unique extension to
the containing algebra is irreducible only when the multiplicity is one.
It is then equivalent to the given faithful representation and has kernel
zero.

Under the quotient form of the Blanchard--Kirchberg homeomorphism, this open
singleton is

```text
{(0,0)} subset Prim(A_0) times Prim(B_0).              (E2)
```

An open singleton in a product forces each coordinate singleton to be open:
choose a basic open neighborhood `U times V` of `(0,0)` contained in (E2).
Then `U={0}` and `V={0}`.

Let `C triangleleft A_0` and `E triangleleft B_0` be the nonzero ideals
corresponding to these two open singletons.  Their primitive spectra are
one-point spaces, so `C` and `E` are simple.  They are nowhere scattered,
because nowhere scatteredness passes from `A,B` to quotients and then to
ideals.  In particular neither `C` nor `E` is elementary.

The product ideal `C tensor_min E` in `A_0 tensor_min B_0` corresponds under
(E1)--(E2) to the same open singleton as `K`.  The ideal/open-set
correspondence therefore gives

```text
C tensor_min E isomorphic K(H).                       (E3)
```

The right side is type I.  By
`type-i-minimal-tensor-reflects-to-factors`, both `C` and `E` are type I.
A nonzero simple type-I C-star algebra is elementary, contradicting the
nowhere scatteredness of `C` and `E`.  Hence `D` is nowhere scattered.

The proof uses min-continuity only through (E1): exactness is what identifies
the primitive quotient with the minimal tensor product of the factor
quotients.  Without exactness, this localization is unavailable.
