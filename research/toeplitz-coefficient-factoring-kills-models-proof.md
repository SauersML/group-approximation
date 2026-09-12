---
rg: 2
id: toeplitz-coefficient-factoring-kills-models-proof
kind: route
title: Direct finiteness of the coefficient ring kills the Toeplitz defect, and simplicity kills the model
target: toeplitz-coefficient-factoring-kills-leavitt-el3-rank-models
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/el3-rank-model-toeplitz-assembly-2026-09-12.md
---

Section 2 of the artifact.
1. In the directly finite ring `D`, `φ(t0) φ(s0) = 1` forces `φ(s0) φ(t0) = 1`, so `φ(e) = 0`.
2. The entrywise map sends `x_12(e)` to `x_12(0) = 1`, so `σ(x_12(e)) = ψ(1) = 1`.
3. `x_12(e) != 1`, and `G = EL_3(R) ≅ R^x` is simple, so `ker σ = G`.
4. The limit version runs the same steps stagewise, up to rank `o(1)`.
