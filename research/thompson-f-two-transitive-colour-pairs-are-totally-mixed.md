---
rg: 2
id: thompson-f-two-transitive-colour-pairs-are-totally-mixed
kind: claim
title: In a 2-transitive action of Thompson's group F, every pair of colours disagrees densely at every point component of a disagreement set, so the Cantor case is a subset-stabilizer model with equal one-sided differences
distinct_from:
  thompson-f-two-transitive-binary-colourings-force-regular-closed: that claim proves density of a bad orbit in each disagreement set and, for exactly two colours, a sum rule; this claim resolves the disagreement by the ordered pair of colours, for any number of colours, and proves each colour pair is dense at every point component
  thompson-f-two-transitive-irrational-orbit-colorings: that claim recovers the stabilizer as the part-wise stabilizer of its orbit partition; this claim shows the set-wise stabilizer of any one part already equals it and, in the Cantor case, that disagreement sets are closures of one-sided differences of translates of that part
  thompson-f-two-transitive-disagreement-sets-are-not-cantor: that claim is the open Cantor half; this claim does not close it but reduces it to a statement about one subset of one irrational orbit and kills the subset models with unequal one-sided differences
  quaternary-cantor-set-passes-disagreement-shape-tests: that claim shows shape data cannot exclude the Cantor case; this claim is a constraint that is not shape data, on colour pairs along a pair
---

Let `F` act on a set `Ω`, `|Ω| ≥ 3`, transitively on ordered pairs of
distinct points. Fix `ω`, put `H = F_ω`, and use `D(ω_1,ω_2)`, `D_0`, bad
orbits, the partition `P_O` of a bad irrational orbit `O` into `H`-orbits
(the **colours**) and the colourings `c_{ω_1} : O → H\O` exactly as in
`thompson-f-two-transitive-disagreement-sets-are-self-similar` and
`thompson-f-two-transitive-irrational-orbit-colorings`. For colours `i ≠ j`
and `ω_1, ω_2 ∈ Ω` put

`D^{ij}(ω_1,ω_2) = cl{ y ∈ O : c_{ω_1}(y) = i, c_{ω_2}(y) = j }`.

It is a closed subset of `D(ω_1,ω_2)`.

1. (Every colour pair occurs.) `D^{ij}(ω_1,ω_2) ≠ ∅` for every ordered pair
   of distinct points and every ordered pair of distinct colours.
2. (Point components are totally mixed.) If `p ∈ D(ω_1,ω_2)` and the
   connected component of `p` in `D(ω_1,ω_2)` is `{p}`, then
   `p ∈ D^{ij}(ω_1,ω_2)` for all colours `i ≠ j`.
3. (Cantor case.) If `D_0` has empty interior, then
   `D^{ij}(ω_1,ω_2) = D(ω_1,ω_2)` for all `ω_1 ≠ ω_2` and all `i ≠ j`.
4. (One part suffices.) If `Q ⊂ O` is a union of colours with
   `∅ ≠ Q ≠ O`, then `H = { g ∈ F : gQ = Q }`. This holds in both cases of
   the dichotomy.
5. (Cantor case as a subset model.) Suppose `D_0` has empty interior and let
   `P` be one colour. Then `aH ↦ aP` is an `F`-equivariant bijection from
   `Ω` onto the orbit `F·P` of subsets of `O`. For all `a, b ∈ F` with
   `aP ≠ bP`,

   `D(aH,bH) = cl(aP ∖ bP) = cl(bP ∖ aP) = cl(aP Δ bP)`.

**What this changes.** The Cantor half
`thompson-f-two-transitive-disagreement-sets-are-not-cantor` now follows from
the following statement about a single subset.

> (†) There is no irrational `F`-orbit `O` and no subset `P ⊂ O`, dense and
> codense in `O`, such that `S = Stab_F(P)` is transitive on
> `F·P ∖ {P}`, `|F·P| ≥ 3`, and for every `f ∈ F` with `fP ≠ P` the sets
> `cl(fP ∖ P)` and `cl(P ∖ fP)` are equal and nowhere dense.

Indeed, if `D_0` is a Cantor set, take a bad irrational orbit (S2.3) and a
colour `P`. Items 4 and 5 give every condition in (†). The statement (†) no
longer mentions colourings, partitions or disagreement sets. The converse,
that a subset as in (†) yields a 2-transitive action of Cantor type, is not
claimed. It would need `D(P,fP) ⊂ cl(fP Δ P)` for the action on `F·P`, and
that inclusion is not proved.

**What this kills.** Every Cantor-type model in which, for some translate,
the closures of the two one-sided differences are unequal. Examples:

- any model with an inclusion `fP ⊊ P` or `P ⊊ fP`, since then one
  one-sided difference is empty while the other is not;
- any model in which some `f` has `fP ∖ P` accumulating at a point `x`
  while `P ∖ fP` stays away from a neighbourhood of `x`. Such a model is a
  "one-way" local move, in which `f` adds points of `P` near `x` without
  removing any;
- more generally, any model with three or more colours in which some pair of
  distinct colours does not occur between two given points near a given point
  component. Such a model is excluded by item 2, in both halves of the
  dichotomy.

This answers the "colourings with three or more colours" gap recorded under
the Cantor claim on 2026-09-19. With any number of colours, the Cantor case
carries two-colour information: the stabilizer of one part, and equal
closures of the two one-sided differences.

**Where it stops.** Item 5 does not give the binary sum rule of
`thompson-f-two-transitive-binary-colourings-force-regular-closed`. That rule
needs `O ∩ D(ω_1,ω_2)` to equal the set where the two-valued colourings
differ. Here the two-valued colouring `y ↦ [y ∈ aP]` can agree at a point
where the full colourings differ. So injectivity of `ω_1 ↦ D(ω,ω_1)` and
closure of `{D(ω,σ)}` under `cl(· Δ ·)` stay open in the Cantor case.

Scope: proved here on 2026-09-19 by swarm agent
`swarm-0917-w17-w17-z-last1`. The proof is elementary. There is no
independent review, and no novelty is claimed.

**Proof:** `thompson-f-two-transitive-colour-pairs-totally-mixed-proof`.
