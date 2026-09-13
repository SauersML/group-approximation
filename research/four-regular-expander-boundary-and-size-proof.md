---
rg: 2
id: four-regular-expander-boundary-and-size-proof
kind: route
title: Compare periodic crossed products with finite matrices below the wraparound radius
target: four-regular-simple-expander-limits-encode-word-graphs
requires:
  - primitive-binary-words-give-four-regular-simple-expanders
  - strong-word-graphs-give-short-primitive-periodic-models
  - binary-subshifts-embed-in-three-marked-kazhdan-groups
  - binary-subshift-language-has-quadratic-group-witnesses
artifacts:
  - research/artifacts/pestov91-four-regular-expanders-and-limits-2026-09-13.md
---

Sections 4 and 5 prove the classification and estimates. The finite
model and the elementary group of its periodic orbit agree on all
relations of length `l` when the least period is greater than `2l`:
the normal-form exponents occupy different cyclic matrix diagonals.
Compactness, the periodic-limit lemma and the marked encoding theorem
then identify every limit and its unique parameter. Simplicity is
equivalent to minimality within this infinite-parameter class.

At word-graph level `2l`, the balanced Euler circuit supplies a period
between `2l+2` and `b_X(2l)` with the required window language, where
`b_X(r)=E+(E-V)(V-1)`, `E=p_X(r+1)` and `V=p_X(r)`.
This proves exact relation agreement. Taking `l=3R` gives a local
embedding of the radius-`R` ball and the finite matrix-group size bound.
Substituting the Sturmian complexity `p_X(r)=r+1` gives `b_X(r)=2r+2`,
linear matrix dimension and the stated quadratic exponent for LEF growth.
