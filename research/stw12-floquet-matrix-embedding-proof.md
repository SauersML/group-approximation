---
rg: 2
id: stw12-floquet-matrix-embedding-proof
kind: route
title: Embed an outer-periodic crossed product into a matrix circle algebra
target: stw12-periodic-actions-over-af-embeddable-algebras
requires:
  - ah-algebras-are-af-embeddable
artifacts:
  - research/artifacts/stw12-periodic-action-af-embedding-audit-2026-08-30.md
---

Let `z` be the coordinate unitary in `C(T)`, number the matrix coordinates
by `0,...,n-1`, and define

```text
pi(a)=diag(a,alpha^(-1)(a),...,alpha^(-(n-1))(a))
       in M_n(A tensor C(T)).                            (F1)
```

Choose `v in U(M(A))` with `alpha^n=Ad(v)`.  In the multiplier algebra of
this matrix algebra, put

```text
V = sum_(j=0)^(n-2) e_(j+1,j) + vz e_(0,n-1).           (F2)
```

Then `V` is unitary.  At the wrap-around coordinate,

```text
v alpha^(-(n-1))(a) v*
  = v alpha^(-n)(alpha(a)) v*
  = alpha(a),
```

while the other coordinates shift without a multiplier.  Hence

```text
V pi(a) V* = pi(alpha(a)).                              (F3)
```

Thus the covariant pair `(pi,V)` integrates to a *-homomorphism

```text
Phi:A rtimes_alpha Z -> M_n(A tensor C(T)).              (F4)
```

Although `V` itself is only a multiplier when `A` is nonunital, every
Fourier monomial `pi(a)V^k` lies in the matrix algebra, so (F4) has the
displayed codomain.  Full and reduced crossed products agree because `Z` is
amenable.

## Faithfulness

For `lambda in T`, let

```text
D_lambda=diag(1,lambda,...,lambda^(n-1))
```

and let `rho_(lambda^n)` rotate the circle coordinate by
`z -> lambda^n z`.  The automorphism

```text
gamma_lambda = Ad(D_lambda) composed with
               (id_A tensor rho_(lambda^n))             (F5)
```

fixes `pi(A)` and sends `V` to `lambda V`.  Hence `Phi` intertwines the
canonical gauge action on the crossed product with `(gamma_lambda)`.
Moreover `pi` is injective, since its zeroth diagonal coordinate is `a`.

If `Phi(x)=0`, average `Phi(x*x)` over (F5).  Gauge equivariance gives

```text
pi(E(x*x))=0,                                            (F6)
```

where `E:A rtimes_alpha Z -> A` is the canonical expectation.  The
expectation is faithful on the reduced crossed product, and `pi` is
injective, so (F6) implies `x=0`.  Therefore `Phi` is an embedding.

## Embed the codomain into AF

Choose an embedding `theta:A -> F` with `F` AF.  There is also an embedding

```text
C(T) -> C(Cantor),
```

obtained by pulling functions back along a continuous surjection from the
Cantor set onto the circle.  The target `C(Cantor)` is AF.  Injectivity of
the minimal tensor product for inclusions gives

```text
M_n(A tensor C(T))
  -> M_n(F tensor C(Cantor)),                            (F7)
```

and the algebra on the right is AF.  Composing (F4) with (F7) proves the
general theorem.  For the AH consequence, use
`ah-algebras-are-af-embeddable`.

**Trust boundary.**  The outer-periodic Floquet representation, compatible
gauge action, faithfulness, and final AF embedding are proved above.  The
only imported class theorem is AF-embeddability of AH algebras.  Standard
background used is faithfulness of the reduced crossed-product expectation,
amenability of `Z`, existence of a Cantor surjection onto every compact
metric space, and closure of AF algebras under minimal tensor products and
matrices.
