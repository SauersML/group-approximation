---
rg: 2
id: hierarchical-tilings-fail-the-free-commutant-test
kind: claim
title: Robinson/Mozes-style hierarchical square tilings have automorphism group Z^2 ⊕ (locally finite), so they fail the F_2 test of target T1; lifting a fibre rotation to a Z-coding is equivalent to an almost 1-1 symbolic Z^2-extension with an expansive horizontal direction; so T1 needs a non-hierarchical data layer on which translations act by cellular automata at every scale
distinct_from:
  profinite-skew-layers-collapse-into-the-equicontinuous-factor: that proves profinite layers carry only abelian automorphisms in the fibre-preserving part; this records, from Hochman's source, that the concrete hierarchical tilings proposed for T1 have locally finite automorphism groups modulo shifts, and reformulates the lifting problem through expansive directions.
  polygonal-anzai-codings-lift-only-finitely-many-rotations: that excludes geometric (polygonal) codings of a twisted base; this excludes the hierarchical skeletons themselves as the source of F_2.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - ra-forces-amenable-commutants-of-uniquely-ergodic-rigid-rows
  - profinite-skew-layers-collapse-into-the-equicontinuous-factor
  - polygonal-anzai-codings-lift-only-finitely-many-rotations
```

**Status.** Item 1 cites a source that was read. Item 2 is a lane proof, elementary; referee bh-ref-d (6e0fb29940) PASS with one repair (existential form of (a)), applied by bh-ra-t2 as the (RA_free) owner. Item 3 is a
heuristic design conclusion. No priority is claimed.

This is a test of the coordinator's candidate for T1: hierarchical, Robinson/Mozes-style simulation
boundaries. T1 needs minimality, freeness and `F_2 ≤ Aut`. **T1 is not built.**

## Statement

1. **The hierarchical skeleton gives only locally finite automorphisms.** Hochman studies the
   nested-square-path `Z^2`-SFTs (*On the automorphism groups of multidimensional shifts of finite type*,
   ETDS 2010; preprint read at source, §6, pp. 17–32), which are Robinson-type hierarchical tilings.
   - For the colored square tiling `X̂` (Theorem 30), `aut X̂ = Z^2 ⊕ G` with `G` locally finite.
   - For its rectangle variant `X_*` (Theorems 38–39), every automorphism is a shift composed with an
     element that eventually fixes the boundary of every level-`n` rectangle and permutes their
     interiors. So `aut X_* = Z^2 ⊕ G` with `G` locally finite.

   - Locally finite groups contain no `F_2`, so these tilings fail the `F_2` test.
   - *Heuristic (not proved here in general).* The mechanism should extend to hierarchical tilings with
     recognizable levels: a cellular automaton of bounded radius cannot move high-level boundaries, so it
     permutes completions inside finitely many shapes per level.
   - This is the combinatorial face of `profinite-skew-layers-collapse-into-the-equicontinuous-factor`.
2. **Lifting is an expansive-direction problem.** Let `Z` carry commuting homeomorphisms `T` and `R`. The
   following are equivalent:
   - (a) `R` lifts to an automorphism `φ` of **some** almost 1-1 symbolic extension `ρ : Y → Z` of
     `(Z, T)` (`ρφ = Rρ`). This existential form is repair (§1) of bh-ref-d, 6e0fb29940. The form for a
     *given* `Y` is false: lifts must preserve fibre cardinalities, so blowing up one `T`-orbit breaks it.
     The time-lift use needs only the existential form.
   - (b) the `Z^2`-system `(Z, T, R)` has an almost 1-1 symbolic extension `Ỹ ⊆ B^(Z^2)` in which the
     horizontal direction is expansive, in the sense of Boyle–Lind (a strip of bounded width around the
     horizontal axis determines the configuration).

   For a group `G` of lifted translations, the same holds with `Z^2` replaced by `Z × G`, and "horizontal
   direction" by "the `Z`-slab". This is the time-lift picture: T1 asks for a rigid Z-slab-expansive
   symbolic model of the joint action of `Z^d × F_2` on the twisted skew product.
3. **Design conclusion (heuristic).** Items 1 and 2, together with the polygonal node, exclude the two
   natural sources of the free commutant:
   - the hierarchical skeleton (locally finite automorphisms);
   - tame geometric codings of the twisted base (finitely many lifts).

   T1 needs a data layer carrying a point of `K = SU(2)`, encoded so that right translation by each
   generator is a cellular automaton at every scale at once. Digit-wise encodings are not of this kind,
   since carries propagate across scales. Orbit-type (Sturmian-like) encodings, in which a translation is
   a shift of the stored word, are the natural candidates. Their hierarchical consistency, meaning that a
   shift of a level-`n` window must agree with the level-`(n+1)` window, is the first open sub-problem.

## Proof of 2

- *(a) ⇒ (b).* Put `Ỹ = {(n, m) ↦ (φ^m y)(n) : y ∈ Y}`. It is closed and invariant under both shifts,
  since `φ` commutes with `σ`.
  - `y ↦` its configuration conjugates `(Y, σ, φ)` to `Ỹ`. So `Ỹ` is an almost 1-1 extension of
    `(Z, T, R)` through `ρ`.
  - The row at `m = 0` determines the whole configuration, so the horizontal direction is expansive.
- *(b) ⇒ (a).* If a strip `S_w` of width `w` determines each configuration, then by compactness the
  entry at `(n, m+1)` is a continuous function of the strip restricted to a bounded window around `n`.
  - So the vertical shift acts on the `Z`-subshift `Y = {strip restrictions}`, with alphabet `B^w`, as a
    cellular automaton. This `Y` is *some* almost 1-1 extension, not a given one. The strip also determines
    the row below it, so the inverse is a cellular automaton too, and the lift is an automorphism (bh-ref-d).
  - `Y → Z` is almost 1-1 as a `Z`-system: its fibres are those of `Ỹ → Z`, because the strip determines
    the configuration.
- The `Z × G` version is identical, with the horizontal strip replaced by the slab `Z × B` for a finite
  ball `B ⊆ G`. ∎

## Lesson for general BH

**The hierarchy that gives rigidity is exactly what cannot carry the free commutant.** Hochman's
hierarchical skeletons have automorphisms that permute finitely many completions per level, so they are
locally finite modulo shifts. That other recognizable hierarchies behave the same way is expected, not
proved. Geometric codings of twisted bases lift finitely many translations.

A rigid row with `F_2 ≤ Aut` must therefore have two layers:
- a hierarchical skeleton, for rigidity;
- a continuous data layer, encoded so that translations are shifts of stored words at every level.

In the language of expansive subdynamics, it is a rigid symbolic model of a twisted `Z^d × F_2`-action
in which the `Z^d`-slab is expansive. The open core of T1 is the scale-consistent orbit encoding of an
`SU(2)` point.
