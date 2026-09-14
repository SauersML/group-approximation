---
rg: 2
id: non-linear-sofic-via-el3-ring-rank-rigidity
kind: route
title: Steinberg ring rigidity plus the Leavitt algebra's lack of rank models makes the Leavitt unit group non-linear-sofic over F_2
target: non-linear-sofic-group
requires:
  - el3-rank-models-factor-through-ring-rank-models
  - leavitt-algebra-has-no-unital-rank-model
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

## Why sufficient

- `R = L_(F_2)(1,2)` is simple and has no unital homomorphism into any rank ultraproduct
  over any field (`leavitt-algebra-has-no-unital-rank-model`). So it meets the hypothesis
  of `el3-rank-models-factor-through-ring-rank-models` with `p = 2`.
- That claim makes every homomorphism `EL_3(R) -> M^x` into a characteristic-two rank
  ultraproduct trivial.
- `EL_3(R) = R^x` (`leavitt-gl-equals-el-and-perfect-unit-group`), and `R^x` is infinite
  and simple (`binary-leavitt-unit-group-is-simple`).
- An `F_2`-linear sofic approximation of `R^x` would give a homomorphism into such an
  ultraproduct that keeps every nontrivial element away from the identity. No such
  homomorphism exists.
- So `R^x` is not `F_2`-linear sofic, which is `non-linear-sofic-group` with `F = F_2`.

## Calibration

- **Independence.** This route needs neither the compression mechanism nor property (T).
  It is independent of `non-linear-sofic-via-f2-rank-row-defect` and of
  `non-linear-sofic-via-leavitt-kaplansky-failure`.
- **A prerequisite that can fail.** The open prerequisite is a class statement about all
  simple characteristic-`p` rings without ring rank models, and it does not mention the
  Leavitt algebra. A linear sofic `EL_3` over any such ring refutes it.
