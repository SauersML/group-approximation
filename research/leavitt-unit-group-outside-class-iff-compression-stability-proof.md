---
rg: 2
id: leavitt-unit-group-outside-class-iff-compression-stability-proof
kind: route
title: A wall at the nine-leaf pair is a nontrivial model of a simple group, hence faithful, and the root defect kills every faithful model under normalization
target: leavitt-unit-group-outside-class-iff-compression-stability
requires: [kazhdan-commutant-compression-stability-is-finitary, leavitt-unit-group-carries-nontrivial-rigid-defect, binary-leavitt-unit-group-is-simple, openai-nine-leaf-leavitt-configuration, sofic-groups-kill-rigid-compression-defects, rigid-compression-defect-normalization-dichotomy]
artifacts:
  - research/artifacts/unified-compression-rigidity-part2-2026-09-12.md
---

Property (U) holds for the four classes (ladder artifact, Section 1): a countable group is in `C`
iff it is isomorphic to a subgroup of some metric ultraproduct `U` of the model groups.

**2 <=> 3.** `kazhdan-commutant-compression-stability-is-finitary`, applied to the rigid
presentation `(F, {u, v})`. `Gamma` and `G_L` are Kazhdan and `u, v` compress `Gamma`
(`openai-nine-leaf-leavitt-configuration`).

**2 => 1.**
1. Suppose `rho : R^x -> U` is injective.
2. `leavitt-unit-group-carries-nontrivial-rigid-defect` gives `j in J <= C_(R^x)(Gamma)` and
   `gamma in Gamma` with `[u j u^-1, gamma] != 1`.
3. `rho(j) in C_U(rho(Gamma))`. By 2 applied to `sigma = rho`,
   `rho(u) rho(j) rho(u)^-1 in C_U(rho(Gamma))`, so `rho([u j u^-1, gamma]) = 1`.
4. This contradicts injectivity. So no `U` contains `R^x`, and by (U) `R^x` is not in `C`.

**1 => 2.**
1. Suppose 2 fails at `sigma : R^x -> U`, i.e. `sigma(R^x)` does not normalize
   `C_U(sigma(Gamma))`.
2. Then `sigma` is nontrivial: the trivial homomorphism has `C_U(sigma(Gamma)) = U`.
3. `R^x` is simple (`binary-leavitt-unit-group-is-simple`), so `ker sigma = 1`.
4. So `R^x` is isomorphic to the countable subgroup `sigma(R^x)` of `U`, and by (U) it lies in `C`.

**Hamming row.** `sofic-groups-kill-rigid-compression-defects` is `DD(sofic)`, which by
`rigid-compression-defect-normalization-dichotomy` gives `NORM` at every pair, hence 2 and 3 for
`C = sofic`. With 2 => 1 this recovers nonsoficity of `R^x`.

No trace condition and no approximation property of `R^x` is assumed anywhere.
