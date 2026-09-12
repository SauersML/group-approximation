---
rg: 2
id: leavitt-pair-vertex-rounding-nonhyperlinearity-proof
kind: route
title: Identify both configuration groups with the unit group and kill the rounding representations by minimal almost periodicity
target: leavitt-pair-vertex-rounding-is-nonhyperlinearity
requires:
  - openai-nine-leaf-leavitt-configuration
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-unit-group-is-minimally-almost-periodic
artifacts:
  - research/artifacts/hyperlinear-nonsofic-l-times-2026-09-12.md
---

The four-step derivation is written in the body of the target.

* **Configuration.** The nine-leaf configuration supplies the pair `Gamma = EL_alpha(R) < G_L = EL_D(R)`
  and property (T) of `Gamma`, so a Kazhdan pair `(F, kappa)` exists.
* **Identification.** `GL = EL` at every rank at least two, together with the prefix-code isomorphisms
  `M_k(R) ~= R`, identifies both `Gamma` and `G_L` with `Q = R^x`.
* **Triviality of rounding targets.** Minimal almost periodicity of `Q` makes every rounding
  representation `pi_n` of `Gamma` trivial.
* **Contradiction.** A trace-preserving model keeps each nontrivial Kazhdan generator at normalized
  distance `sqrt 2` from `1`. So rounding holds exactly when no trace-preserving model of `G_L` exists,
  i.e. when `G_L ~= Q` is not hyperlinear.
