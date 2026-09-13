---
rg: 2
id: torus-tiling-modules-restrict-to-smaller-scales
kind: claim
title: A module of the torus tiling algebra at scale D is a module at every smaller scale on the same torus
distinct_from:
  sft-tiling-module-dimensions-and-periods-must-diverge: that bounds the dimensions and periods of witnesses; this says witnesses descend in scale, so witnesses at unboundedly many scales give witnesses at every scale
artifacts:
  - research/artifacts/un-labbe-torus-decider-inflation-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Ω` be a `Z^2`-SFT, `k` a field, `Λ ≤ Z^2` of finite index, and `D' <= D`. Every
module of the torus tiling algebra `𝒯_(D,Λ)(Ω,k)` (relations (T1)–(T3) of
`torus-quantum-tilings-decide-matriciality-of-sft-rings`) is a module of `𝒯_(D',Λ)(Ω,k)` through the same generators.

So in Theorem 1(d) of `torus-quantum-tilings-decide-matriciality-of-sft-rings` it suffices to find nonzero
finite-dimensional modules at unboundedly many scales.

Route: `torus-tiling-modules-restrict-to-smaller-scales-proof` (artifact §2).
