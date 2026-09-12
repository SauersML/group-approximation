---
rg: 2
id: injective-automata-over-fg-groups-are-virtually-formalizable
kind: claim
title: Every injective binary automaton over a finitely generated group has a left inverse that is formalizable after regrouping along some finite-index subgroup
distinct_from:
  injective-binary-automata-have-formalizable-left-inverses: that asked for formal pairs without regrouping and is refuted by the marker involution over Z; this allows regrouping along a finite-index subgroup, where that involution is formalizable.
  marker-involution-over-rationals-is-not-virtually-formalizable: that refutes the regrouping statement over Q, which is not finitely generated; this is the statement for finitely generated groups, which is all the Kaplansky payoff needs.
  injective-binary-automata-are-stably-formalizable: that allows identity ancilla tracks; this allows regrouping along a finite-index subgroup, and no implication between the two is known.
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
---

**OPEN.** Let `Γ` be a finitely generated group and `n >= 1`. Every injective automaton `tau` on
`(F_2^n)^Γ` has a finite-index subgroup `H <= Γ` and a left-inverse automaton `sigma` such that the
pair, regarded as `H`-automata on `(F_2^(n[Γ:H]))^H`, is formalizable.

The payoff is `stable-finiteness-forces-binary-surjunctivity`, through the route
`virtual-formalizability-reduces-surjunctivity-to-kaplansky`.

## Attempts

- **Marker flips.** Subset-stable marker flips satisfy the claim whenever a finite-index normal
  subgroup avoids the window (`subset-stable-marker-flips-are-virtually-formalizable`). That covers
  the marker involution over `Z`, which regroups along `4Z`.
- **Why finitely generated.** Over `Q` the induced marker involution is not formalizable after any
  regrouping (`marker-involution-over-rationals-is-not-virtually-formalizable`). The payoff route
  only needs the finitely generated memory subgroup.
- **Reversible automata over `Z^d`.**
  - A block permutation along translates of a fundamental domain of `bZ^d` is a word of indicator
    track shears over `bZ^d`: each block meets every track once, and a permutation of `{0,1}^B` is a
    product of hypercube-edge transpositions.
  - Translations are formal.
  - So a decomposition of every reversible automaton into block permutations and translations would
    give the claim for bijective automata over `Z^d`.
  - Kari's decompositions for `d = 1, 2` are recalled, not read from source, so no node relies on
    them. For `d >= 3`, structural reversibility is open.
- **Groups without finite-index subgroups.** There `H = Γ`, and the claim is plain formalizability
  on `n` tracks.
  - `formalizable-binary-pairs-over-biorderable-groups-are-affine` never applies to a nontrivial
    finitely generated perfect group.
  - The reason: a finitely generated bi-orderable group has a maximal proper convex subgroup, which is
    normal with Archimedean quotient, so the group maps onto `Z`.
  - So on `R^x` and on finitely generated simple hosts, no one-track classification constrains the
    claim.
- **Strict automata.** On a host with stably finite `F_2[Γ]`, no strict pair is formalizable after
  regrouping, by the payoff route. A proof must therefore produce Kaplansky failures from strict
  automata.
- **Where it stops.** Every formal pair known after regrouping is a gate word, hence bijective. No
  mechanism produces formal representatives for a strict automaton.
- **Block decompositions (gk-fz-kari).** For bijective automata over `Z`, the imported Kari decomposition
  into block permutations along translated partitions reduces virtual formalizability to sitewise tame
  permutations, invertible linear maps and structural gates (`reversible-automata-over-integers-are-block-permutation-words`,
  route `kari-words-give-virtual-formalizability-over-integers` into
  `reversible-binary-automata-over-integers-virtually-formalizable`). Words of formally invertible pieces
  represent bijections, so decompositions reach no strict automaton: for strict `tau` a formal pair needs a
  formally non-invertible layer, and on memory groups without proper finite-index subgroups block methods
  reach only equivariant partitioned words (artifact `partitioned-and-regrouped-formalizability-2026-09-12.md`).
