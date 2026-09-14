---
rg: 2
id: acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead
kind: claim
title: For any finite flag 2-complex L that is acyclic but not aspherical, H_L refutes Eilenberg--Ganea or a Whitehead counterexample exists
distinct_from:
  eilenberg-ganea-or-whitehead-is-false: that is Bestvina--Brady Theorem 8.7 for a spine of the Poincaré homology sphere; this isolates the only input that proof uses about L, namely pi_2(L) nonzero, and states the dichotomy for every such L.
artifacts:
  - research/artifacts/hl-whitehead-bestvina-brady-2026-09-13.md
---

**ESTABLISHED** through `acyclic-nonaspherical-l-dichotomy-proof`.
Unreviewed. No novelty is claimed: this is Bestvina--Brady's argument with
the hypothesis on `L` made explicit.

Let `L` be a finite flag simplicial complex of dimension at most 2 with
`H~_*(L; Z) = 0` and `pi_2(L) != 0`. Let `G_L` be the right-angled Artin group
of the 1-skeleton of `L`, and `H_L` the kernel of the homomorphism `G_L -> Z`
sending every standard generator to `1`. Then:

1. `H_L` is finitely generated, of type FP, not finitely presented, and has
   cohomological dimension 2.
2. If `H_L` does not have geometric dimension 2, it is a counterexample to
   `eilenberg-ganea-conjecture`.
3. If `H_L` has geometric dimension 2, there is a contractible 2-complex `Y`
   and a finite connected subcomplex `K` of `Y` with `pi_2(K) != 0`. So `K` is
   a counterexample to `whitehead-asphericity-conjecture`. Moreover
   `pi_1(L)` is a retract of `pi_1(K)`.

**Examples.** Every acyclic finite 2-complex with finite nontrivial
fundamental group `G` satisfies `pi_2(L) != 0`. The universal cover is a
simply connected finite 2-complex with Euler characteristic `|G| chi(L) = |G|`,
so `pi_2(L) = H_2(L~) = Z^(|G|-1)`. The spine of the Poincaré homology sphere
is one such complex.

**Does not cover.** Acyclic aspherical `L`, such as triangulated presentation
complexes of acyclic groups of geometric dimension 2. There the shadow argument
yields no spherical class.
