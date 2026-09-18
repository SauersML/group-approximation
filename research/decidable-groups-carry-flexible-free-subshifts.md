---
rg: 2
id: decidable-groups-carry-flexible-free-subshifts
kind: claim
title: Every infinite finitely generated group with solvable word problem carries a nonempty free subshift with decidable language, separated gluing, and computable points
distinct_from:
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is (M2), which asks for a MINIMAL effective free subshift; this gives a free subshift with decidable language that is transitive-by-gluing but not minimal, which is all that universal points need.
  decidable-groups-have-universal-hyperaperiodic-points: that is the pointwise premise (U)+(H); this is the subshift from which such a point is built, by route universal-hyperaperiodic-points-via-decidable-free-subshifts.
  gjs-countable-groups-have-free-minimal-subflows: that gives free subflows for every countable group non-effectively; this is effective, with a decidable language and a gluing property, for groups with solvable word problem.
  decidable-groups-carry-free-subshifts-with-decidable-language: that is premise (D) of bh-g1-universal-point, free plus decidable language for finitely presented groups; this adds separated gluing, computable points and a computable freeness radius, for all finitely generated decidable groups, so it implies (D).
---

**PROVED (lane proof at design level, bh-g1-simulation, 2026-09-18; unreviewed).** Proof:
`identifier-markers-give-decidable-free-subshifts`.

## Statement

Let `Γ` be an infinite finitely generated group with solvable word problem, with the conventions
of `free-products-with-z-inherit-m2-from-universal-points`. There is a nonempty subshift
`X ⊆ C^Γ`, with `|C| = 4`, such that:
1. **(H) for every point.** There is a computable `R` such that for all `x ∈ X`, `s ≠ 1` and
   `g ∈ Γ`, some `a ∈ B(R(s))` has `x(ag) ≠ x(asg)`. In particular `X` is free.
2. **Decidable language.** `L(X)` is decidable.
3. **Separated gluing.** There is a computable `G`: any finite family of `L(X)`-patterns of
   radius `≤ ρ`, placed pairwise at distance `≥ G(ρ)`, and consistently with an `L(X)`-pattern
   they avoid, lies in `L(X)`.
4. **Computable points.** Every pattern of `L(X)` extends computably to a computable point of
   `X`.

## What it rests on

- **Freeness.** It needs no randomness. At each scale, maximal separated markers carry
  identifiers that are distinct within the relevant radius. Two positions at displacement `s`
  would then see equal markers with equal identifiers at distance `≤ 6r_{|s|} + |s|`.
- **Decidability.** It comes from flexibility. Greedy marker systems have no dead ends beyond a
  computable horizon (lemma (E)), so extendability is a finite check. Pockets of the Cayley
  graph are detected, not avoided.

## Lesson for general BH

On a decidable group, hyperaperiodicity and decidability of the language are cheap together,
provided one gives up minimality. The only thing that ever made (M2) hard was recurrence, and
the Bass–Serre tree of `Γ * Z` supplies recurrence. So the input side of the existence gate needs
only this flexible, transitive-by-gluing free subshift, and every decidable group has one. See
`universal-hyperaperiodic-points-via-decidable-free-subshifts` for the consequence.
