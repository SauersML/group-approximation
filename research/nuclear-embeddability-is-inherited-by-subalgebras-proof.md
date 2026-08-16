---
rg: 2
id: nuclear-embeddability-is-inherited-by-subalgebras-proof
kind: route
title: Compose the embedding with the nuclear one, using isometry of injective star maps
target: nuclear-embeddability-is-inherited-by-subalgebras
requires: []
artifacts:
  - GroupApproximation/Analysis/CStarExactness.lean
---

## Why sufficient

Machine-checked, no `sorry`, no axiom, no literature premise.

**Complete positivity, and that ⋆-homomorphisms have it.**
`IsCompletelyPositive φ` says every positive matrix over the source goes to a
positive matrix over the target under the entrywise map.
`isCompletelyPositive_of_starAlgHom`: applying a non-unital ⋆-homomorphism
entrywise is again a ⋆-homomorphism on `CStarMatrix`, so it carries
`star N * N` to `star (N.map f) * (N.map f)`.  `isCompletelyPositive_id` and
`IsCompletelyPositive.comp` give the identity and closure under composition,
which is all the bookkeeping the two permanence proofs need.

**The definitions.**  `FinDimCStarAlgebra` bundles a finite-dimensional complex
C-star algebra with its instances, with the carrier in `Type` — nothing is lost,
since such an algebra is a finite direct sum of matrix algebras, and bundling
keeps the approximant's universe independent of the universes of the algebras
being approximated, which is what makes `IsNuclearMap` composable at all.
`IsNuclearMap`, `IsNuclearCStarAlgebra` and `IsNuclearlyEmbeddable` are then as
in the claim, with `CStarAlgebraBundle` letting the existential in the last one
avoid an instance binder.

**Heredity.**  `IsNuclearMap.comp_injective_starAlgHom` then
`IsNuclearlyEmbeddable.of_injective_starAlgHom`: given `A → B` injective and
`B → C` a nuclear embedding, the composite is injective, and it is nuclear
because the approximants for the finite set `image` of a finite `F ⊆ A` pull back
— the key input is `NonUnitalStarAlgHom.norm_map`, that an injective
⋆-homomorphism of C-star algebras is isometric, so the point-norm estimates
transfer with no loss.

**Nuclear implies nuclearly embeddable.**
`IsNuclearCStarAlgebra.isNuclearlyEmbeddable`: take the identity embedding, whose
nuclearity is the hypothesis.

**Non-vacuity.**  `isNuclearCStarAlgebra_complex`: `ℂ` is nuclear, approximated
by itself.

## What is deliberately not proved

No equivalence with exactness (that is Kirchberg, and needs tensor products), no
closure under extensions (Kirchberg--Wassermann, and needs quotients as C-star
algebras), and no statement about any group algebra.  The route establishes the
two permanence facts and nothing more; `IsCStarShortExact` is defined in the same
module with `comp_eq_zero` as the one consequence drawn from it, so that the
shape of the missing statements is visible rather than absent.
