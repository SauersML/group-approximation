---
rg: 2
id: finite-evc-unimodular-weyl-groups-have-finite-efin
kind: claim
title: In a group with a finite E_VC model, the Weyl group of an infinite virtually cyclic subgroup with unimodular commensurator has a finite E_FIN model
distinct_from:
  finite-evc-model-restricts-to-commensurators: that claim gives finite models for the commensurator N_G[C]; this claim gives finite models for the normalizer quotient N_G(C)/C, which needs the extra unimodularity hypothesis
  finite-evc-model-implies-fp-and-bvc: that claim concerns G and Weyl groups of finite subgroups (von Puttkamer–Wu Proposition 1.1); this claim concerns Weyl groups of infinite virtually cyclic subgroups
artifacts:
  - research/artifacts/finite-evc-commensurator-restriction-2026-09-16.md
---

**Statement.** Let `G` admit a finite model `X` for `E_VC G`, and let `C <= G` be infinite
virtually cyclic. Suppose the modular homomorphism

`Δ_C : N_G[C] -> Q_{>0}^×`, `Δ_C(g) = [gCg^{-1} : E]/[C : E]` for `E` of finite index in
`gCg^{-1} ∩ C`,

is trivial. Then:

- the fixed set `X^C` has finitely many `N_G(C)`-orbits of cells;
- `N_G(C)` has type `F_infinity`;
- `X^C` is a finite model for `E_FIN(N_G(C)/C)`.

If `C = <c>` is infinite cyclic, then `Z_G(c)` has type `F_infinity` and `Z_G(c)/<c>` admits a
finite `E_FIN` model.

**Sharpness of the hypothesis.** Take `G = Z[1/p] ⋊_p Z` and `C = <1>` (Lück–Weiermann,
arXiv:math/0702646, Example 2.6).

- The Bass–Serre tree `T` is a finite model for `E_{G[C]}(G)`, and `Δ_C(t) = 1/p`.
- `N_G(C) = Z[1/p]` is not finitely generated, and the fixed tree `T^C` has infinitely many
  `N_G(C)`-orbits of vertices.

So no argument that uses only the commensurator data can drop unimodularity.
