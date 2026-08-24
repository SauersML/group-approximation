---
rg: 2
id: approximation-radical-calculus
kind: claim
title: One four-step calculus reaches both extremes of MF invisibility
root: true
distinct_from:
  shadow-kleene-saturation-metatheorem: that metatheorem is a single step of this calculus, the compiler that turns a HALT-surviving/NONHALT-erased word family into a full-radical group; this claim is that the four steps compose, and in particular that the separating half computes radicals exactly rather than only saturating them.
  hyperlinear-to-mf-saturation-compiler: that is the analytic backend of the saturation step alone and takes a routing map as an input; this claim concerns the composition of all four steps and the two opposite endpoints they reach.
  wreath-compression-mf-radical: that computes the MF radical of one explicit family; this asserts the general calculus of which that computation is one instance of the separating step.
  self-aware-finite-approximation-trichotomy: that classifies the forms self-aware finite approximation can take; this organizes a subgroup-valued mechanism -- produce, renormalize, saturate, separate -- and says nothing about self-awareness.
  radical-automorphization: that is the renormalization step alone, a statement about one surjective endomorphism; this is the four-step composite in which that step is used.
artifacts:
  - GroupApproximation/Endpoint/ApproximationRadicals.lean
  - GroupApproximation/Sofic/RadicalAutomorphization.lean
  - research/artifacts/radical-renormalization-2026-08-23.md
---

Write `Rad(G)` for the radical of an approximation theory: the intersection of
the kernels of all homomorphisms from `G` into a fixed class of targets.  The
MF corpus contains a complete four-step calculus for these subgroups, and the
two opposite extremes of the theory both follow from it.

**Produce.**  `R_{infinity->2}` is a fully invariant normal subgroup and
Kazhdan compression puts a nontrivial word inside it.  What is produced is
weaker than radical membership: the inclusion
`Rad_MF(G) <= R_{infinity->2}(G)` is strict in general.

**Renormalize.**  If `R:G->G` is a surjective endomorphism with
`ker R <= Rad(G)`, then `K_infty(R) = union_n ker(R^n) <= Rad(G)`, the
descended map on `G/K_infty(R)` is an automorphism, and that quotient is the
largest one on which `R` becomes injective.  One local forgotten relation
therefore propagates through every scale.

**Saturate.**  If the routed image of the produced word normally generates the
output, then `Rad_MF(Q) = Q`: the output is 2-generated, finitely presented,
and every homomorphism from it to an MF group is trivial, as is every
homomorphism from any of its nontrivial quotients.

**Separate.**  If the quotient by the forced kernel is MF, the lower bound is
exact: `Rad_MF(G) = N`.  For the compression wreath family the resulting
subgroup is simultaneously five radicals with one universal visible quotient,
and the family separated only inside that invisible part is pairwise
noncommensurable.

The two extremes are therefore both attainable from one local defect:

```text
compute exactly what MF forgets        (separate)
make MF forget absolutely everything   (saturate)
```

and what is forgotten need not be simple: one fixed finitely presented group
has an undecidable word problem entirely inside its MF radical, and the hard
words lie in `[Rad_MF, G]` rather than in a centre.

**Lean status.**  The renormalizing and separating steps and the analytic half
of saturation are formalized and re-exported through
`Endpoint/ApproximationRadicals`.  The group-theoretic routing input of the
saturation step (Higman embedding, Hull small cancellation, the acylindrical
envelope) is an external hypothesis in Lean, and the strictness of
`Rad_MF < R_{infinity->2}` has no Lean witness.
