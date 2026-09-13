---
rg: 2
id: labbe-shift-is-a-toral-rotation-coding
kind: claim
title: Labbé's 19-tile Wang shift is the coding of the toral rotation by golden-mean steps through a polygonal Markov partition with fiber cardinalities 1, 2, 8
distinct_from:
  minimal-aperiodic-wang-shift-exists: that imports minimality and aperiodicity from Labbé's 2018 paper; this imports the 2019 Markov partition, the maximal equicontinuous factor, the fiber cardinalities, and the polygon geometry of the partition.
artifacts:
  - research/artifacts/labbe-shift-wall-rigidity-2026-09-13.md
---

**ESTABLISHED (import).** Let `φ = (1+√5)/2` and `R_U^n(x) = x + φ^(-2) n` on `T^2 = R^2/Z^2`. There is a
polygonal partition `P_U` of `T^2` into 19 atoms with the following properties.

1. **Coding.** `Ω_U` equals the symbolic system `X_(P_U, R_U)`, which is minimal and aperiodic.
2. **Markov partition.** `P_U` is a Markov partition, so it gives a symbolic representation. Every tiling `w`
   determines a unique point `f(w)`, and `f` is a factor map.
3. **Equicontinuous factor.** The rotation is the maximal equicontinuous factor, and the set of fiber
   cardinalities of `f` is `{1, 2, 8}`.
4. **Ergodicity.** `Ω_U` is strictly ergodic, and measure-isomorphic to the rotation with Haar measure.
   Hence `h_top(Ω_U) = 0`.
5. **Genericity.** The coding map on points whose orbits avoid `∂P_U` is injective, and its image is dense.
6. **Geometry (read from the source figure).** The vertices of `P_U` have coordinates in
   `{0, φ^(-3), φ^(-2), φ^(-1), 2φ^(-2), 1}`. Every boundary segment has direction `(1,0)`, `(0,1)`,
   `(1,-1)` or `(1,-φ)`, and each direction occurs away from the frame.

Route: `labbe-shift-is-a-toral-rotation-coding-citation`.
