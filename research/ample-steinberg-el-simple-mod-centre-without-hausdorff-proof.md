---
rg: 2
id: ample-steinberg-el-simple-mod-centre-without-hausdorff-proof
kind: route
title: Unital simple Steinberg algebra plus Hausdorff-free local annihilation feed the Lean ring criterion
target: ample-steinberg-el-simple-mod-centre-without-hausdorff
requires:
  - steinberg-algebras-have-local-annihilation
  - local-annihilation-makes-projective-el-simple
  - elementary-groups-over-fg-rings-have-property-t
artifacts:
  - research/artifacts/un-open-3-grigorchuk-characteristic-2026-09-13.md
---

Artifact §2.
1. `1 = 1_(𝒢⁰)`: the unit space is a compact open bisection, so `A` is unital. Two-sided `k`-algebra ideals are then
   two-sided ring ideals, so `A` is a simple ring.
2. `steinberg-algebras-have-local-annihilation` assumes only an ample groupoid with compact infinite unit space and uses
   no Hausdorffness. Its review (`un-review-2026-09-13-part1.md` §1) notes that the argument holds for non-Hausdorff
   `𝒢`. So `A` satisfies the Lean predicate `LocalAnnihilation`.
3. `local-annihilation-makes-projective-el-simple` (hypotheses exactly `3 ≤ card ι`, `IsSimpleRing R`,
   `LocalAnnihilation R`) gives: every normal subgroup of `EL_n(A)` is central or everything, and `S_n` is simple.
4. **Infinite.** An infinite compact totally disconnected Hausdorff space has infinitely many disjoint nonempty
   clopens, so `A` is infinite. If `e_12(a−b)` is central, then `[e_12(a−b), e_23(1)] = e_13(a−b) = 1` gives `a = b`.
   So `e_12(A)` injects into `S_n`.
5. **(T).** For finite `k` and finitely generated `A`, `elementary-groups-over-fg-rings-have-property-t` gives (T), and
   (T) passes to quotients.
