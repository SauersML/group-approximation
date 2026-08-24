---
rg: 2
id: mf-camouflage-integral-representation-geometry-proof
kind: route
title: Put the camouflage kernel in the finite residual and pass from functors to schemes
target: mf-camouflage-preserves-integral-representation-geometry
requires:
  - mf-camouflage-surgery
  - finite-residual-quotients-are-universal-linear-reflections
---

Every finite group is MF.  The factorization theorem for `C_d(Q)` therefore
says that every map from `C_d(Q)` to a finite group factors uniquely through
`pi_Q`.  Hence

```text
ker(pi_Q) <= R_fin(C_d(Q)).                           (IRG5)
```

The finite-residual reflection theorem applied to `(IRG5)` gives `(IRG1)`.
Taking the underlying module to be the free module `A^n` gives `(IRG2)`.

For a finitely presented group `G=<x_1,...,x_s | r_1,...,r_t>`, the functor

```text
A |-> Hom(G,GL_n(A))
```

is represented by the closed subscheme of `GL_n^s` cut out by the matrix
entries of `r_j-1`.  It is therefore affine and of finite type over `Z`.
The bijections `(IRG2)` are natural in `A`; Yoneda's lemma turns them into the
scheme isomorphism `(IRG3)`.  Precomposition commutes with simultaneous matrix
conjugation, so `(IRG3)` is `GL_n`-equivariant.  The quotient-stack and
invariant-ring conclusions follow.

Over a field, every finite-dimensional module is finitely presented.  The
equivalence `(IRG1)` is the identity on underlying vector spaces and respects
tensor products.  Tannaka reconstruction therefore gives identical
proalgebraic completions and identical Hopf algebras of matrix coefficients.

Let `rho` be a `k`-point of `Rep_n(Q)`.  For every local Artinian `k`-algebra
`A`, naturality of `(IRG2)` identifies the fibers over `rho` of

```text
Rep_n(Q)(A) -> Rep_n(Q)(k)
```

and the corresponding map for `C_d(Q)`.  Equivariance also identifies the
conjugation morphisms between lifts.  This proves equality of framed and
unframed deformation groupoids and all stated local consequences.

When `Q` is MF, the camouflage theorem computes a nontrivial kernel killed by
every MF-target map, while amalgam normal form keeps its generator nontrivial.
Thus `C_d(Q)` is non-MF despite `(IRG1)--(IRG4)`.
