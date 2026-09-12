---
rg: 2
id: a-t-menable-groups-have-no-rigid-compression-defect
kind: claim
title: Rigid pairs inside an a-T-menable group are finite and carry no compression defect
distinct_from:
  sofic-groups-kill-rigid-compression-defects: that is the criterion DD(sofic) about sofic ambient groups; this shows every rigid pair contained in an a-T-menable subgroup has trivial defect in every ambient group, so no DD criterion can certify that an a-T-menable group is nonapproximable.
  finite-infranormal-subgroup-is-normal: that is the finite normalizer lemma; this is its consequence for rigid pairs of an a-T-menable group, where property (T) forces finiteness.
---

**ESTABLISHED.** Let `L` be a countable group with the Haagerup property, let
`H` be any group containing `L`, and let `Gamma <= G <= L` be a rigid pair: `Gamma` and
`G` have property (T), and `Gamma` is infranormal in `G`. Then

- `G` is finite, `Gamma` is normal in `G`, and
- `[g z g^-1, gamma] = 1` for all `g in G`, `z in C_H(Gamma)`, `gamma in Gamma`,
  so the rigid defect `D_H(G, Gamma)` is trivial.

**Consequence.** For every approximation class `C` in
`rigid-compression-defect-normalization-dichotomy`, the criterion `DD(C)` says
nothing about whether an a-T-menable group lies in `C`: its hypothesis is only
met by finite pairs with trivial defect. The same holds for the group-level
Kun--Thom Theorem A mechanism and for the OpenAI criterion: both need an
infinite nonnormal infranormal Kazhdan subgroup, and none exists in `L`. So
the Kazhdan compression mechanism can prove nonapproximability of an
a-T-menable group only through a larger ambient group. Nonapproximability of
the ambient group does not descend to the subgroup. Examples: Thompson's
`F`, `T` and `V`, free groups, and groups acting properly on CAT(0) cube
complexes.

Derivation: `a-t-menable-groups-have-no-rigid-compression-defect-proof`.
