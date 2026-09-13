---
rg: 2
id: continuum-many-infinite-minimal-binary-subshifts
kind: claim
title: The Sturmian codings X_α (α irrational) are continuum many pairwise distinct infinite minimal subshifts of {0,1}^Z
artifacts:
  - research/artifacts/un-open-5-marked-subshift-groups-2026-09-13.md
---

For irrational `α ∈ (0,1)`, let `X_α ⊆ {0,1}^Z` be the closure of the codings
`c(y)_n = 1_[1−α,1)(y + nα mod 1)`, for `y ∈ [0,1)`. Then:
- `X_α` is an infinite minimal subshift;
- in every point of `X_α`, the frequency of the symbol `1` equals `α`, uniformly over windows.

Hence `α ↦ X_α` is injective, and there are continuum many pairwise distinct infinite minimal subshifts over a
two-letter alphabet. (These are the Sturmian subshifts of Morse–Hedlund.)

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part1.md` §1.6): PASS,
classical.** The half-open arc cylinders, bounded recurrence, minimality and the counting identity
`#{t < n : {y+tα} ∈ [1−α,1)} = ⌊y+nα⌋ − ⌊y⌋ ∈ {⌊nα⌋, ⌊nα⌋+1}` were re-derived.
