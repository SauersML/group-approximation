---
rg: 2
id: eilenberg-ganea-conjecture
kind: claim
title: Every group of cohomological dimension 2 has a 2-dimensional Eilenberg--MacLane space
root: true
distinct_from:
  whitehead-asphericity-conjecture: that concerns subcomplexes of aspherical 2-complexes; this concerns the geometric dimension of groups of cohomological dimension 2.
  bestvina-brady-poincare-kernel-has-geometric-dimension-three: that is a specific counterexample statement, which refutes this conjecture if established.
refuted_by:
  - bestvina-brady-poincare-kernel-has-geometric-dimension-three
artifacts:
  - research/artifacts/hl-whitehead-bestvina-brady-2026-09-13.md
---

**OPEN.** The Eilenberg--Ganea conjecture, in the form recalled by
Bestvina--Brady (Invent. Math. 129 (1997), p. 461, read from the Springer PDF
on MSI): "Recall that the Eilenberg-Ganea conjecture states that if a group H
has cohomological dimension 2, then it has a 2-dimensional Eilenberg-Mac Lane
space K(H,1)."

**Links.** `eilenberg-ganea-or-whitehead-is-false` (Bestvina--Brady
Theorem 8.7): this conjecture or `whitehead-asphericity-conjecture` is false.

## Attempts

1. **Bestvina--Brady kernels (2026-09-13).** The kernel `H_L` for a flag
   triangulation `L` of a spine of the Poincaré homology sphere has
   cohomological dimension 2. Geometric dimension 3 would refute this
   conjecture: `bestvina-brady-poincare-kernel-has-geometric-dimension-three`.
   Bestvina--Brady's closing remark (p. 470) conjectures that it does, through
   an unproved statement about ε-maps. Undecided.
2. **Cockcroft presentations over residually nilpotent augmentation ideals
   (2026-09-17).** `cockcroft-2-complexes-over-rn-cd-two-groups-are-aspherical`
   extends Gersten's finite asphericity criterion to 2-complexes of any size.
   Hypotheses: the fundamental group has cd ≤ 2 and ⋂ Iⁿ(ZG) = 0, which covers
   every subgroup of a right-angled Artin group.

   From it, `rn-cd-two-group-has-gd-two-iff-cockcroft-presentation` proves a
   two-directional reduction:
   - gd `H_L` = 2 iff `H_L` has a presentation F/N whose relators are Z-linearly
     independent in N/[F,N];
   - any such presentation has infinitely many generators.

   Consequently, Eilenberg--Ganea for residually torsion-free nilpotent cd-2 groups
   becomes a linear-independence problem for relators modulo [F,N], instead of the
   vanishing of a ZG-module. This does not decide `H_L`.
