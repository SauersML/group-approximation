---
rg: 2
id: reversible-binary-automata-over-integers-virtually-formalizable
kind: claim
title: Every reversible binary automaton over the integers is formalizable after regrouping along some mZ
distinct_from:
  subset-stable-marker-flips-are-virtually-formalizable: that covers marker-flip involutions through a direct shear word along a finite-index subgroup avoiding the window; this is every reversible binary automaton over Z, through a block-permutation decomposition.
  injective-automata-over-fg-groups-are-virtually-formalizable: that is the open statement for every injective automaton over every finitely generated group, strict ones included; this is its bijective special case over Z, reached through Kari-type block permutations.
  injective-binary-automata-are-stably-formalizable: that allows identity tracks with Z-equivariant representatives and covers strict automata over every group; this allows regrouping and covers only bijective automata over Z.
artifacts:
  - research/artifacts/partitioned-and-regrouped-formalizability-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

**OPEN.** For every bijective automaton `tau` on `{0,1}^Z` there is `m >= 1` such that `tau`,
regrouped along `mZ`, has `mZ`-equivariant representatives forming a formal two-sided pair with its
inverse.

This is a calibration only: `Z` is amenable, so there is no surjunctivity content. It would show that
regrouping plus block decompositions dissolve the one-track rigidity of
`formalizable-binary-pairs-over-biorderable-groups-are-affine` for every reversible automaton over
`Z`, not only for marker flips.

## Attempts

- **Through Kari.** The route `kari-words-give-virtual-formalizability-over-integers` reduces the claim
  to the imported decomposition `reversible-automata-over-integers-are-block-permutation-words`, which
  is open here.
- **Direct words.** Marker-flip involutions are covered without the import
  (`subset-stable-marker-flips-are-virtually-formalizable`).
- **Partition lemma, partly derived** (artifact, Section 3): for neighbourhoods `{0,1}` / `{−1,0}` the
  local rule factors through `(rho, lambda)`, and `a -> (lambda(a), rho(a))` is injective. The counting
  step is missing.
