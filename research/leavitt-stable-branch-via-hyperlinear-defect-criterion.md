---
rg: 2
id: leavitt-stable-branch-via-hyperlinear-defect-criterion
kind: route
title: The hyperlinear defect criterion makes the binary Leavitt unit group HS-stable
target: leavitt-steinberg-hs-stable
requires:
  - hyperlinear-groups-kill-rigid-compression-defects
  - leavitt-unit-group-carries-nontrivial-rigid-defect
  - leavitt-unit-hs-stable-iff-nonhyperlinear
---

Let `R = L_(F_2)(1,2)` and `H = R^x`.

1. `leavitt-unit-group-carries-nontrivial-rigid-defect` gives the nine-leaf
   rigid pair `Gamma = EL_alpha(R) <= G_L = EL_D(R) <= H`: both groups are
   Kazhdan and `Gamma` is infranormal in `G_L`. It also gives `j` in
   `J = V_(1000) <= C_H(Gamma)`, a compressor `u` and `gamma in Gamma` with
   `[u j u^-1, gamma] != 1`.
2. If `H` were hyperlinear, `hyperlinear-groups-kill-rigid-compression-defects`,
   applied to `H` and this pair with `g = u` and `z = j`, would make that
   commutator trivial. So `H` is not hyperlinear.
3. By `leavitt-unit-hs-stable-iff-nonhyperlinear`, nonhyperlinearity of `H` is
   normalized-HS stability of `H = St_5(R)`. That is the target.

**What this records.** The positive branch of the hyperlinear defect criterion
proves the stable Leavitt--Steinberg branch itself, not only
`non-hyperlinear-group`. The route consumes the criterion at one ambient group,
`R^x`, and one pair, the nine-leaf configuration. A proof of the criterion for
that group and that pair is therefore enough for the stable branch.

Companion: `rigid-defect-witness-from-hyperlinear-leavitt-unit-group` records
the other direction. The unstable branch refutes the criterion.
