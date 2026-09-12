---
rg: 2
id: mf-camouflage-preserves-integral-representation-geometry
kind: claim
title: MF camouflage preserves integral representation geometry and deformation theory
root: true
artifacts:
  - research/mf-camouflage-integral-representation-geometry-proof.md
distinct_from:
  camouflage-prescribes-representation-spaces: that identifies topological spaces of unitary representations and their stable asymptotic models; this identifies representation categories over every commutative ring, affine schemes over the integers, quotient stacks, and all classical infinitesimal deformations.
  mf-camouflage-surgery: that gives a targetwise Hom-bijection for MF targets; this applies the finite-residual reflection theorem to every finitely presented module representation, including targets that are not MF groups.
---

Let `C_d(Q)` be the camouflage group and

```text
pi_Q:C_d(Q)->Q
```

its split quotient.  If `Q` is finitely generated, then for every nonzero
commutative ring `A` there is a canonical equivalence

```text
Rep_A^fp(C_d(Q)) ~= Rep_A^fp(Q).                     (IRG1)
```

It preserves the underlying module, intertwiners, scalar extension, sums,
tensor products, and finite exact diagrams.  In particular, for every
`n>=1`, precomposition gives a natural bijection

```text
Hom(C_d(Q),GL_n(A)) ~= Hom(Q,GL_n(A)).                (IRG2)
```

Suppose now that `Q` is finitely presented.  Both groups then have affine
finite-type representation schemes over the integers, and `(IRG2)` is induced
by a `GL_n`-equivariant isomorphism

```text
Rep_n(C_d(Q)) ~= Rep_n(Q)                            (IRG3)
```

for every `n`.  Consequently they have the same integral universal
representation algebras, the same quotient stacks

```text
[Rep_n(C_d(Q))/GL_n] ~= [Rep_n(Q)/GL_n],             (IRG4)
```

and the same affine character quotients in every characteristic.

For every field `k`, `(IRG1)` identifies their finite-dimensional tensor
categories together with the forgetful functor to vector spaces.  Their
proalgebraic completions over `k` and their finite-dual Hopf algebras are
therefore canonically isomorphic.

Finally, every representation `rho:Q->GL_n(k)` has exactly the same framed
and unframed deformations after pullback to `C_d(Q)`: for every local Artinian
`k`-algebra `A`, the lift groupoids over `A` agree.  Hence completed local
rings, tangent spaces, and classical obstruction behavior are identical.

If `Q` is MF, `C_d(Q)` is nevertheless non-MF.  Thus the entire integral
linear representation geometry, in every rank and characteristic and to all
infinitesimal orders, does not determine whether a finitely presented group is
MF.
