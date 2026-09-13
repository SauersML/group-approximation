---
rg: 2
id: continuum-many-infinite-minimal-binary-subshifts-proof
kind: route
title: Cylinders of a rotation coding are arcs, arcs are visited with bounded gaps, and letter frequency recovers α
target: continuum-many-infinite-minimal-binary-subshifts
requires: []
artifacts:
  - research/artifacts/un-open-5-marked-subshift-groups-2026-09-13.md
---

Artifact §5, a self-contained proof.
1. For a word `w` of length `n`, the set `J_w = {y : c(y)_[0,n) = w}` is a finite union of half-open arcs with
   endpoints in `{−tα mod 1 : t ≤ n}`. If `w` is legal, then `J_w ≠ ∅`, so it has positive length.
2. The finite segments `{tα mod 1 : t < N}` become `ℓ`-dense, so every orbit enters an arc of length `ℓ` within
   `N(ℓ)` steps. Every legal word therefore occurs in every `c(y)` with bounded gaps. That property is closed,
   so it passes to all of `X_α`. Every point then contains all legal words, and `X_α` is minimal.
3. **Counting.** `#{t < n : y+tα mod 1 ∈ [1−α,1)} = ⌊y+nα⌋ − ⌊y⌋`, which lies in `{⌊nα⌋, ⌊nα⌋+1}`
   (telescoping, since `{z} ∈ [1−α,1)` iff `⌊z+α⌋ = ⌊z⌋+1`). So window frequencies of `1` are within `1/n`
   of `α` in every `c(y)`, and by continuity in every point of `X_α`. Hence `X_α` is aperiodic (so infinite),
   and `X_α ∩ X_β = ∅` for `α ≠ β`.
