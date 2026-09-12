---
rg: 2
id: rigid-defect-witness-from-hyperlinear-leavitt-unit-group
kind: route
title: A hyperlinear binary Leavitt unit group is a hyperlinear group with a nontrivial rigid defect
target: hyperlinear-group-carries-nontrivial-rigid-defect
requires:
  - binary-leavitt-unit-group-hyperlinear
  - leavitt-unit-group-carries-nontrivial-rigid-defect
---

Let `R = L_(F_2)(1,2)`, and suppose `R^x` is hyperlinear. Take `H = R^x` and
the nine-leaf pair `Gamma = EL_alpha(R) <= G_L = EL_D(R)` of
`leavitt-unit-group-carries-nontrivial-rigid-defect`. Both groups are Kazhdan,
`Gamma` is infranormal in `G_L`, and some `j in J <= C_H(Gamma)` and
`gamma in Gamma` satisfy `[u j u^-1, gamma] != 1`. That is the target, with an
explicit group and pair.

**What this records.** The unstable Leavitt--Steinberg branch refutes the
hyperlinear defect criterion `hyperlinear-groups-kill-rigid-compression-defects`
at an explicit configuration. The branch is `binary-leavitt-unit-group-hyperlinear`,
by `steinberg-instability-from-leavitt-unit-hyperlinear` and
`leavitt-unit-hyperlinear-from-steinberg-instability`. With
`leavitt-stable-branch-via-hyperlinear-defect-criterion`, the three questions
line up:

- the criterion implies that `R^x` is stable;
- instability of `R^x` implies that the criterion fails.

What stays open between them is whether the criterion can fail at some other
group while `R^x` is stable.
