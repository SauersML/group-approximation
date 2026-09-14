---
rg: 2
id: marker-involution-over-rationals-is-not-virtually-formalizable
kind: claim
title: The six-cell marker involution induced to the rationals admits no formal pair after regrouping along any finite-index subgroup
distinct_from:
  binary-left-inverse-pairs-need-not-be-formalizable: that is non-formalizability as a Z-automaton, which regrouping along 4Z escapes; this is the same rule over Q, which has no proper finite-index subgroup, so no regrouping escapes.
  subset-stable-marker-flips-are-virtually-formalizable: that formalizes marker flips by regrouping along a finite-index subgroup avoiding the window; this shows that without finite-index subgroups the conclusion fails for the same rule.
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
  - research/artifacts/binary-formalizability-refutation-2026-09-12.md
---

On `{0,1}^Q`, let `tau` flip cell `q` exactly when
`(x_(q−3), x_(q−2), x_(q−1), x_(q+1), x_(q+2), x_(q+3)) = (0, 0, 1, 1, 0, 0)`. Then:
- `tau` is a bijective involution, acting on each coset `q + Z` as the marker involution over `Z`;
- for every finite-index subgroup `H <= Q`, the pair `(tau, tau)` is not formalizable as
  `H`-automata;
- `tau` is its own unique left inverse, so no left inverse of `tau` is formalizable after any
  regrouping.

**Consequence.** "Every injective binary automaton has a left inverse that is formalizable after
regrouping along some finite-index subgroup" is false over `Q`. The live regrouping statement,
`injective-automata-over-fg-groups-are-virtually-formalizable`, is for finitely generated groups.
The payoff route localizes to the finitely generated memory subgroup first.

Proof: Section 5.3 of the first artifact.
