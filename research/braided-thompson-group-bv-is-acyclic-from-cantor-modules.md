---
rg: 2
id: braided-thompson-group-bv-is-acyclic-from-cantor-modules
kind: route
title: bV is integrally acyclic if the Cantor power function modules are V-acyclic
target: braided-thompson-group-bv-is-acyclic
requires:
  - cantor-power-function-modules-are-v-acyclic
  - thompson-v-is-integrally-acyclic
artifacts:
  - research/artifacts/zp-braided-v-rational-acyclicity-2026-09-13-part1.md
  - research/artifacts/zp-braided-v-rational-acyclicity-2026-09-13-part3.md
---

Integral version of `braided-thompson-group-bv-is-rationally-acyclic-proof`.
Only Step B used rational coefficients essentially; this route replaces it by
the required claim.

1. **Step A integrally.** `H_*(Conf_n(R^2); Z)` is torsion-free with the
   Gerstenhaber basis, so the support decomposition and the colimit (part 1,
   A1–A5) hold over `Z`. For `q ≥ 1`,
   `H_q(K; Z) ≅ ⊕_{m=q+1}^{2q} C_c(Conf_m(C), Z) ⊗_{Z[Σ_m]} W_{m,q}` with
   `W_{m,q}` free abelian of finite rank.
2. **Step C integrally.** Lemmas C1, C2, C4 and C5 of part 3 are exact-sequence
   arguments valid over `Z`. With `cantor-power-function-modules-are-v-acyclic`
   in place of C3, `C_c(Conf_m(C), Z)` is V-acyclic.
3. **C6 integrally.** Lexicographic order on `{0,1}^N` gives a clopen fundamental
   domain for the free `Σ_m`-action on `Conf_m(C)`, so `C_c(Conf_m(C), Z)` is a
   free `Z[Σ_m]`-module. Tensoring it over `Z[Σ_m]` with a free resolution of
   `W_{m,q}` gives a resolution of `C_c ⊗_{Z[Σ_m]} W_{m,q}` by direct sums of
   V-acyclic modules. The first-quadrant hyperhomology spectral sequence then
   gives V-acyclicity.
4. **Assembly.** In the integral Lyndon–Hochschild–Serre spectral sequence of
   `K → bV → V`, rows `q ≥ 1` vanish, and row 0 vanishes in positive degrees
   (`thompson-v-is-integrally-acyclic`). So `H_n(bV; Z) = 0` for `n ≥ 1`.
