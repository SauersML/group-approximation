---
rg: 2
id: labbe-scale-two-commutation-crosses-faults-at-distance-five
kind: claim
title: In the scale-2 presentation of Labbé's shift, context splits certify commutation at 26 of the 40 offsets at sup-distance 5, including both axis fault normals, where determinism certifies none; at the resonant offset (6,0) explicit window representations exclude every certificate supported in windows of height up to 11
distinct_from:
  labbe-shift-is-quantum-rigid-iff-rigid-at-scale-two: that fixes the scale (J_2 = 0 decides rigidity); this measures how far J_2-certificates actually reach, and where they are provably non-local.
  labbe-wang-shift-crossed-product-is-finitely-presented: that is the open rigidity question; this is partial, exact progress on it in both directions.
artifacts:
  - research/artifacts/gq-bh-g2-labbe-j2-contextual-probe.md
---

**ESTABLISHED (2026-09-18).** This is an exact computation (Slurm job, one core, 51 s) that applies the lane proof in
`contextual-closure-certifies-quantum-rigidity`. It is unreviewed. `Ω_U` is Labbé's 19-tile shift and `C_2` its
scale-2 presentation: 229 legal `5×5` patterns, commutation within sup-distance `4`.

## Statement

1. **Determinism alone certifies nothing.** The determinism closure at `D = 2` is exactly `B_4` in the region
   `|v|_∞ <= 10`. At `D = 1` it is exactly `B_2`.
2. **Context splits cross the faults.** In `C_2`, `[P_0^a, P_v^b] = 0` for all letters `a, b` at 26 of the 40
   offsets with `|v|_∞ = 5`.
   - Three antipodal pairs are certified directly by context splits with `5×5` windows: `±(5,2)`, `±(2,5)`, `±(2,−5)`.
   - These unlock determinism steps for ten more pairs, among them `(±5,0)` and `(0,±5)`. These are the offsets along
     the axis fault normals, which no determinism argument can cross by itself.
   - For `(5,0)` a direct two-box context split also works: for window heights `5` to `13`, with margins `0` and `1`,
     there are no double faults. The same holds for `(0,5)`.
3. **The frontier.** The 14 uncertified offsets at distance 5 are `(±5,±5)`, `(±5,±4)`, `(±4,±5)` and `±(3,−5)`.
   - They are the diagonal offsets, along the normals of the anti-diagonal and diagonal fault families, plus one pair
     near the golden direction.
   - While they stay open, the commuting rectangles stop at `3×6`, `5×5` and `6×4`. Context splits then certify no
     offset at distances `6` to `20` (searched with up to 40 window pairs per offset).
4. **Non-locality at the resonant offset (6,0).** For the windows `K_H = [0,6] × [0,2H]`, item 3 of the contextual
   node gives explicit `2`-dimensional representations of `C_2(K_H)` with `[P_(0,H), P_(6,H)] ≠ 0` for `H = 2, …, 5`.
   - The number of double-fault band patterns is `7, 5, 3, 1`, for bands of columns `[1,4]` or `[2,5]`.
   - So **no certificate of the `(6,0)` commutation, of any degree, is supported in a `7 × 11` window.**
   - At `H = 6` (height `13`) the band double faults vanish.
   - For `(0,6)` they vanish already at width `7`.

## Interpretation (heuristic, torus model)

- **Vertical faults.** The lines `x ∈ {0, 1, φ}` fault three adjacent columns. A double fault at separation `L` along
  `e_1` needs column `0` at the right end of one fault triple and column `L` at the left end of another. That means
  `L ≡ φ − 1 (mod φ^2)`, to the precision to which the band pins the torus point.
  - `L = 5` is at distance `0.854` from this, so it is not resonant: certified.
  - `L = 6` is at distance `0.146`, so it is resonant: walls until height `~ 1/0.146 ≈ 6.8`. Observed: they vanish at
    `H = 6`.
- **Horizontal faults.** The lines `y ∈ {0, φ}` fault two adjacent rows, so the condition along `e_2` is
  `L + 1 ≡ 0`. For `L = 6` the distance is `0.854`, and the walls vanish at `H = 3`.
- **Predicted resonant separations.**
  - Along `e_1`: `6, 11, 19`, at distances `0.146, 0.090, 0.056`.
  - Along `e_2`: `7, 12, 20`.

  These are Fibonacci offsets. The context height needed grows linearly in `L`.

## What this changes for E2

`J_2(Ω_U) = 0` (Labbé rigidity) is now a precise multiscale question. Certifying resonant distance `L` along one fault
normal needs commuting context windows of transverse size about `L`. That in turn needs commutation along the other
normals up to about `2L`, and the diagonal fault normals are where the process first stops, at distance 5.
- A proof must close this induction along the golden continued fraction. The next test is contexts that are not
  rectangles, stacked across the diagonal faults.
- A refutation must be a genuinely contextual family of dimension `>= 3` (`labbe-shift-is-wall-rigid` rules out
  global two-dimensional ones). It must live on the diagonal resonances.

## Lesson for general BH

Rigidity of toral-rotation SFTs (the calibration objects for gate E2) is decided by resonances, not by scale.
Determinism fails at every fault normal. Context splitting crosses faults wherever the two one-sided failures do not
coincide. Where they do coincide, at Fibonacci-resonant separations for golden codings, certificates are provably
non-local in exact proportion to the resonance depth. Any rigid SFT built for Track A should therefore be chosen to
have non-resonant, or at least badly approximable, fault geometry. The contextual closure is the mechanical test of
this.
