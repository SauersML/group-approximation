---
rg: 2
id: stw87-virtually-cyclic-actions-have-dimension-one
kind: claim
title: Every free minimal zero-dimensional action of an infinite finitely generated virtually cyclic group has nuclear dimension one
distinct_from:
  stw87-zero-dimensional-minimal-actions-have-dimension-one: that gives the upper bound for all virtually nilpotent groups and lower bounds from an infinite abelianization or specifically D_infinity; this closes every finite-kernel cyclic and dihedral type in the virtually cyclic classification.
  stw87-asdim-zero-one-equality: that computes the full uniform Roe algebra of an asymptotic-dimension-one metric space; this computes arbitrary free minimal zero-dimensional transformation-group quotients.
artifacts:
  - research/artifacts/stw87-virtually-cyclic-parity-audit-2026-08-30.md
---

Let `G` be an infinite finitely generated virtually cyclic group.  For every
free minimal action of `G` on a nonempty compact zero-dimensional Hausdorff
space `K`, without a metrizability assumption,

```text
dim_nuc(C(K) crossed_product_r G)=1.                    (VC1)
```

The lower bound is new for the finite-abelianization, dihedral-type groups.
Every infinite virtually cyclic group is of exactly one of the following
types.

1. It maps onto `Z` with finite kernel.  The Pimsner--Voiculescu boundary of
   the implementing unitary is the nonzero unit class.
2. It has an amalgam decomposition

   ```text
   G=G_1 *_F G_2,
   G_1,G_2,F finite,             [G_1:F]=[G_2:F]=2.     (VC2)
   ```

   For every pointwise free action on a nonempty compact zero-dimensional
   space—not necessarily minimal—the crossed product is not locally AF.
   Pimsner's exact sequence for crossed products by groups acting on trees
   makes its `K`-groups the cokernel and kernel of the two index-two
   orbit-sum maps.  Directed-limit continuity supplies the same sequence for
   nonmetrizable `K`.  The constant parity class either gives nonzero
   two-torsion in `K_0`, or its divisibility produces a nonzero odd-valued
   class in `K_1`.

The upper bound in `(VC1)` is the virtually nilpotent zero-dimensional
crossed-product theorem.  Thus the type dichotomy supplies the missing
lower bound for every infinite virtually cyclic group, including finite
extensions of `D_infinity` whose abelianization may be finite.

Consequently every minimal closed `G`-invariant subset `M subset beta G`
gives a quotient

```text
C*_u(G)/K(ell^2(G)) ->> C(M) crossed_product_r G
```

of nuclear dimension exactly one.  This agrees with `asdim(G)=1`; it is a
complete computation of these minimal boundary quotients, not a new proof
of the already known uniform-Roe equality in asymptotic dimension one.
