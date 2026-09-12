---
rg: 2
id: central-simple-leavitt-tensor-simplicity-proof
kind: route
title: Feed division in B ⊗ L and the trivial centre into the abstract root-detection theorem
target: central-simple-leavitt-tensor-unit-groups-are-simple
requires:
  - leavitt-tensor-hosts-acyclic-steinberg-and-fp
  - binary-leavitt-elementary-group-is-simple
  - leavitt-center-is-coefficient-field
artifacts:
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
  - GroupApproximation/Leavitt/RootDetectionBinary.lean
  - GroupApproximation/Leavitt/ElementarySimplicity.lean
---

The Lean theorems behind `binary-leavitt-elementary-group-is-simple` are
stated for an arbitrary ring `R`.

- `rootDetection_of_leavittFamily` (`RootDetectionBinary.lean`) needs:
  - `3 <= card ι`;
  - a `LeavittFamily R`;
  - `hdiv : ∀ x, x != 0 -> ∃ a b, a * x * b = 1`;
  - `hcentral`: every central invertible element equals `1`.
- `isSimpleGroup_of_rootDetection` (`ElementarySimplicity.lean`) then needs
  `hdiv`, nontriviality of the elementary group, and root detection. Its
  conclusion is `IsSimpleGroup (elementaryGroup ι R)`.

For `R = B ⊗ L`:
- **Leavitt family.** `e, f, e*, f*` in `1 ⊗ L`.
- **`hdiv`.** Artifact Corollary 2.3, the case `s = 1` of the division lemma
  inside `leavitt-tensor-hosts-khanh-transfer-proof`. It uses only simplicity
  of `B`.
- **`hcentral`.** Over a field, `Z(B ⊗ L) = Z(B) ⊗ Z(L)`. With `B` central
  and `Z(L) = F_2` (`leavitt-center-is-coefficient-field`), every central unit
  lies in `F_2^x = {1}`.
- **Nontriviality.** `x_12(1) != 1`.

This proves part 1. For part 2:
- leaf coordinates give `R^x ≅ GL_3(R)`;
- `leavitt-tensor-hosts-acyclic-steinberg-and-fp`(2) gives `GL_3(R) = E_3(R)`;
- the roots `x_12(s_0^k)` are pairwise distinct, so the group is infinite;
- `[x_12(1), x_23(1)] = x_13(1)`, so it is nonabelian.
