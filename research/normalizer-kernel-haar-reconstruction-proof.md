---
rg: 2
id: normalizer-kernel-haar-reconstruction-proof
kind: route
title: Fourier-dualize the regular abelian kernel and its conjugation action
target: normalizer-kernel-generation-forces-haar-action
requires: []
---

Because `K` lies in the abelian algebra `A`, it is an abelian group.  The
regular-trace condition `(NK1)` restricts to
`tau(k)=delta_(k,1)` on `K`.  Hence the algebraic representation of `C[K]`
is isometric in `L^2`, extends normally to `L(K)`, and is injective.  The
hypothesis `W*(K)=A` makes it onto.  Fourier duality gives `(NK2)`, including
the Haar trace.

Since every element of `Gamma` normalizes `A` and conjugation preserves the
subgroup `K=Gamma cap U(A)`, `K` is normal in `Gamma`.  Conjugation therefore
gives a homomorphism `Gamma/K -> Aut(K)`, whose Pontryagin dual is an action on
`K-hat` by continuous group automorphisms preserving Haar measure.

Finally `(NK1)` identifies the normal representation of `Gamma` with its
canonical group von Neumann algebra, and total generation makes this
identification onto `M`.  For a section `s:Gamma/K->Gamma`, multiplication
has the form `s(q)s(r)=c(q,r)s(qr)` with `c(q,r) in K`; this is exactly the
`A`-valued cocycle crossed-product presentation of the group extension.  A
splitting makes it the ordinary semidirect-product Haar crossed product.

