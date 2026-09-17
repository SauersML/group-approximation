---
rg: 2
id: rn-cd-two-group-has-gd-two-iff-cockcroft-presentation
kind: claim
title: A cd-2 group with residually nilpotent augmentation ideal has geometric dimension 2 iff some presentation has relators Z-independent in N/[F,N]
distinct_from:
  cockcroft-2-complexes-over-rn-cd-two-groups-are-aspherical: that is the asphericity criterion for a single 2-complex; this is the resulting equivalence for the group, the translation into presentations, and the consequences for H_L.
  bestvina-brady-poincare-kernel-has-geometric-dimension-two: that is the open alternative itself; this proves it is equivalent to H_L having a Cockcroft presentation, which must have infinitely many generators.
  eilenberg-ganea-or-whitehead-is-false: that is the Bestvina--Brady dichotomy; this is an equivalence for one side of it, in terms of relators modulo [F,N].
artifacts:
  - research/artifacts/hl-whitehead-bestvina-brady-2026-09-13.md
---

**ESTABLISHED** (proposed; referee requested) through
`rn-cd-two-gd-two-iff-cockcroft-presentation-proof`. This is a strict reduction
and both directions are proved.

**Theorem.** Let G be a group with cd G = 2 and ⋂ₙ Iⁿ(ZG) = 0. This holds, for
example, for any subgroup of a finitely generated residually torsion-free
nilpotent group, such as a subgroup of a right-angled Artin group. The following
are equivalent.

- **(i)** gd G = 2.
- **(ii)** G = π₁(X) for some Cockcroft 2-complex X.
- **(iii)** G has a presentation G = F(S)/N with a normally generating set of
  relators R ⊂ N whose images in the abelian group N/[F,N] are Z-linearly
  independent. They are then automatically a Z-basis of N/[F,N].
- **(iv)** G = π₁(X) for a 2-complex X in which every finite subcomplex is
  Cockcroft.

**Consequences for Bestvina--Brady kernels.** Let L be a finite flag 2-complex
that is acyclic but not aspherical, for example a flag triangulation of a spine of
the Poincaré homology sphere. Then:

- **(a)** gd `H_L` = 2 iff `H_L` has a presentation whose relators are Z-linearly
  independent in N/[F,N].
- **(b)** Every such presentation has infinitely many generators. More generally,
  for any group G of type FP₂ that is not finitely presented, every aspherical
  2-complex with fundamental group G still has infinitely many 1-cells after a
  maximal tree is collapsed. This part needs cd G = 2 but not the
  augmentation-ideal hypothesis.
- **(c)** Suppose some presentation of `H_L` has relators Z-independent in
  N/[F,N]. Then `whitehead-asphericity-conjecture` fails, by
  `acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead` read in the
  gd = 2 direction.
- **(d)** Any 2-dimensional K(`H_L`,1) is a directed union of finite Cockcroft
  subcomplexes. Combining Gersten's finite criterion (arXiv:1501.06875) with the
  asphericity theorem for free groups, each finite subcomplex that is not
  aspherical has a fundamental group of cohomological dimension at least 3.

**What changed.** The condition π₂ = 0 is a vanishing statement about a
ZG-module. Condition (iii) replaces it by Z-linear independence in an abelian
group. No ZG-module structure and no homotopy of 2-complexes is involved: the
question is only whether some presentation of `H_L` has no integral relation
among its relators modulo [F,N].

**Honest scope.**
- This does not decide gd `H_L`. It changes the object the problem is about.
- The translation (ii) ⟺ (iii) for a single presentation complex is classical:
  for any presentation, the Hurewicz image of π₂ is the kernel of
  Z^(R) → N/[F,N]. The new input is Theorem A, which turns "Cockcroft" into
  "aspherical" for infinite complexes over these groups.
- The content of (iii) is a relation-gap-type question. N/[F,N] is free abelian
  here, and integer row operations on relators (replacing r by r·s) stay inside
  the set of normal generators. The obstruction is a relator whose image lies in
  [F,N] but which cannot be discarded without shrinking the normal closure.
- N/[F,N] contains H₂(G) with quotient N[F,F]/[F,F] ⊆ F^ab. So the target of
  (iii) is a free abelian group that can be computed from H₂(G) and the generators.
