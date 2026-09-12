---
rg: 2
id: leavitt-nested-rigid-defect-proof
kind: route
title: A nontrivial element of a simple nonabelian group is noncentral
target: leavitt-units-carry-nested-rigid-defect
requires:
  - openai-nine-leaf-leavitt-configuration
  - binary-leavitt-elementary-group-is-simple
artifacts:
  - research/artifacts/defect-window-automata-2026-09-12.md
---

Derivation (artifact Proposition 5.2).

- **The configuration.** The nine-leaf configuration supplies:
  - Kazhdan `Gamma` and `G`;
  - `G = <Gamma, u, v>` with `u, v` compressing `Gamma`, so `Gamma` is infranormal;
  - `[Gamma, J] = 1` and `u J u^-1 <= Gamma`.
- **A noncentral target.** For nontrivial `z in J`, the element `u z u^-1` is a
  nontrivial element of `Gamma ≅ EL_3(R)`. That group is simple and nonabelian, so its
  center is trivial and some `gamma` fails to commute with `u z u^-1`.
