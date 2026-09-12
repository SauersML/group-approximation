---
rg: 2
id: leavitt-units-carry-nested-rigid-defect
kind: claim
title: The binary Leavitt unit group carries a nested nontrivial rigid compression defect
distinct_from:
  openai-nine-leaf-leavitt-configuration: that verifies the hypotheses of the expander-matching criterion; this extracts from them a rigid defect whose conjugated commuting element lies inside the compressed Kazhdan subgroup and is noncentral there.
  surjunctive-groups-carry-invisible-rigid-defects: that exhibits non-nested rigid defects in surjunctive groups; this exhibits a nested one in the Leavitt unit group, the configuration those carriers lack.
artifacts:
  - research/artifacts/defect-window-automata-2026-09-12.md
---

**ESTABLISHED** by `leavitt-nested-rigid-defect-proof`.

Let `R = L_(F_2)(1,2)`. In the nine-leaf configuration take:
- `Gamma = EL_alpha(R) ≅ EL_3(R)` and `G = EL_D(R)`, both Kazhdan;
- the compressors `u, v`, which generate `G` together with `Gamma`;
- `J = V_(1000)`, which centralizes `Gamma`, with `u J u^-1 = V_(0001) <= Gamma`.

For every nontrivial `z in J`, some `gamma in Gamma` has

    [u z u^-1, gamma] != 1,     with  u z u^-1 in Gamma.

This is a rigid defect of the rigid pair `Gamma <= G <= R^x` that is **nested**: the
conjugated commuting element lies inside `Gamma` itself.

By `surjunctive-groups-carry-invisible-rigid-defects` it is sofic-invisible, as is every
element of `R^x`.
