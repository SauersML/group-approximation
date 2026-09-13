---
rg: 2
id: self-similar-sft-matricial-iff-one-torus-module-proof
kind: route
title: Inflate the base module along the substitution to unbounded scales, descend to every scale, and apply the torus criterion
target: self-similar-sft-matricial-iff-one-torus-module
requires:
  - torus-quantum-tilings-decide-matriciality-of-sft-rings
  - torus-tiling-modules-restrict-to-smaller-scales
  - constant-shape-substitutions-inflate-torus-tiling-modules
artifacts:
  - research/artifacts/un-labbe-torus-decider-inflation-2026-09-13.md
---

Artifact §4.

- **(⇒)** Theorem 1(d) of `torus-quantum-tilings-decide-matriciality-of-sft-rings` at `D = 3`.
- **(⇐)** Put `D_0 = 3` and `D_(m+1) = s_min(D_m - 1)`.
  - By `constant-shape-substitutions-inflate-torus-tiling-modules` the base module gives nonzero modules at scale
    `D_m` on `Z^2/S^mΛ`, and `D_(m+1) >= D_m + 1`.
  - By `torus-tiling-modules-restrict-to-smaller-scales` there are nonzero modules at every scale.
  - Theorem 1(d) (⇐) of the torus criterion gives the unital embedding in a matrix ultraproduct. ∎
