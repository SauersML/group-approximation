---
rg: 2
id: property-t-free-st20-collapse-transfers-to-el12
kind: claim
title: Full MF collapse of binary-Leavitt St20 transfers internally to the manuscript's EL12
artifacts:
  - research/property-t-free-st20-collapse-transfers-to-el12-proof.md
  - GroupApproximation/Steinberg/Basic.lean
  - GroupApproximation/Leavitt/LeavittRankEquivalence.lean
  - GroupApproximation/Sofic/FullRadicalClosureProperties.lean
  - non_mf_groups_exist.tex
---

Let

```text
R = L_(F_2)(1,2),
Delta = St_20(R),
H = EL_12(R).
```

Then the following implication is Property-`(T)`-free:

```text
Rad_MF(Delta) = Delta  ==>  Rad_MF(H) = H.
```

The implication uses only the canonical Steinberg projection, the explicit
binary-prefix matrix self-similarity, and functoriality of the MF radical.  In
particular, it is not an appeal to the existing rank-twelve full-radical
theorem, whose current proof is Kazhdan-mediated.

