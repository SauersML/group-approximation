---
rg: 2
id: smart-induced-map-alternates-head-direction
kind: claim
title: SMART induced on genuine level-0 moves reverses the head direction at every step, so -1 is a continuous eigenvalue; a height-2 renormalization would need i as well
distinct_from:
  smart-level-zero-return-map-factors-onto-3-adic-odometer: that gives the Z_3 part of the factor (and a Z/2 for the map induced on all level-0 configurations); this identifies the Z/2 eigenfunction of the phase-2 induced map S as the head direction, readable from the state alone.
  renormalization-heights-force-eigenvalue-roots: that is the general root criterion; this applies it to S at height 2.
  smart-induced-map-has-brick-local-height-3-renormalization: that is the height-3 renormalization giving BS(1,3); this records what a height-2 one (BS(1,2)) would additionally need.
artifacts:
  - research/artifacts/gq-affq-smart-eigenvalue-test.md
---

**ESTABLISHED** through `smart-induced-map-alternates-head-direction-proof`. Items 1 and 2 are
an elementary lane proof, not independently reviewed. Item 3 is a finite-radius computation and
proves nothing beyond what it states.

**Setting.** `S` is the first-return map of SMART's moving-tape map to `Y`, the genuine level-0
moves (`smart-induced-on-genuine-moves-has-exact-tripling`). The direction `δ(y) ∈ Z/2` is `0` for
`▶_2, ⊳_2` (right-moving) and `1` for `◀_2, ⊲_2` (left-moving).

**Statement.**
1. **Alternation.** `δ(S y) = δ(y) + 1` for every `y ∈ Y`. So `-1` is a continuous eigenvalue
   of `S`, with eigenfunction `(-1)^δ` depending only on the state.
2. **Height-2 criterion.** Let `B = {δ = 0}`. `S` is the height-2 tower over `S^2|_B`. A height-2
   renormalization of `S` (which by `renormalizable-thompson-elements-give-baumslag-solitar` would
   give `BS(1,2) ≤ 3V`) is a brick-local conjugacy from `S^2|_A` to `S` for some tower level
   `A`. By `renormalization-heights-force-eigenvalue-roots` it requires `i ∈ E(S)`. Since
   eigenfunctions of a minimal map are unique up to constants, that means the direction
   eigenfunction has a continuous square root: a clopen `C ⊆ B` with `S^2 C = B ∖ C`.
3. **Computation (MSI).** No `Z/4`-eigenfunction of `S` is a function of the radius-`r` window
   for any `r ≤ 6`. For `r ≥ 7` the sampled windows rarely repeat, so the test is uninformative
   there. The `Z/3` calibration is consistent from `r = 1`, and `Z/2` from `r = 0`. See the
   artifact.

**Reading.** The letter sequence of `S`-visits is substitutive for `▶ ↦ ▶◀⊳`, `◀ ↦ ◀▶⊲`,
`⊳ ↦ ▶⊲⊳`, `⊲ ↦ ◀⊳⊲` (`smart-level-zero-return-map-factors-onto-3-adic-odometer`). Item 1 is the
height-2 structure of that constant-length substitution. By Dekking's theorem on constant-length
substitutions (quoted from memory, not re-read), its maximal equicontinuous factor is
`Z_3 × Z/2`, so `i` is not an eigenvalue of the letter factor. Whether `S` itself has the extra
eigenvalue `i` is open. If it does not, SMART cannot serve as a base for `BS(1,2)` at all, which
matches the branching-parity obstruction of `crossing-move-hierarchies-have-odd-branching`.
