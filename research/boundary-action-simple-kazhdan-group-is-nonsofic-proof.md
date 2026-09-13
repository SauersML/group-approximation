---
rg: 2
id: boundary-action-simple-kazhdan-group-is-nonsofic-proof
kind: route
title: Leavitt family plus the Lean nonsoficity theorem, and a corner copy that avoids the central scalars
target: boundary-action-simple-kazhdan-group-is-nonsofic
requires:
  - boundary-crossed-product-carries-leavitt-family
  - d-ary-leavitt-groups-nonsofic-over-finite-fields
  - steinberg-elementary-groups-are-simple-mod-centre
artifacts:
  - research/artifacts/un-hyperlinear-paradox-2026-09-13.md
---

§2 of the artifact.

1. `R_∂` is a nontrivial countable `k`-algebra carrying a unital `d`-ary Leavitt family
   (`boundary-crossed-product-carries-leavitt-family`). By `d-ary-leavitt-groups-nonsofic-over-finite-fields`
   (Lean `LeavittFamily.elementary_not_isSofic`), `EL_N(R_∂)` is nonsofic for `N >= 2`.
2. **Corner copy.** Put `e = s_1 t_1`; since `d >= 2`, `1 - e != 0`.
   - `theta(x) = s_1 x t_1` is a unital ring isomorphism `R_∂ -> e R_∂ e`, with inverse `y ↦ t_1 y s_1`.
   - `Phi(X) = X + (1-e) I_N` is an injective homomorphism `EL_N(eR_∂e) -> EL_N(R_∂)`, sending `e_ij(r)` to `e_ij(r)`.
   - If `Phi(X) = λ I_N`, compressing by `1 - e` gives `λ = 1`. So `psi = Phi ∘ EL_N(theta)` embeds `EL_N(R_∂)` into
     `EL_N(R_∂)` meeting `k^x I_N` trivially.
3. So `psi(EL_N(R_∂))` maps injectively to `EL_N(R_∂)/C` for every `C ≤ k^x I_N`. Subgroups of sofic groups are
   sofic, so `EL_N(R_∂)/C` is nonsofic.
4. The boundary groupoid is minimal and effective (`boundary-action-elementary-simple-kazhdan-proof`, steps 1–2).
   By `steinberg-elementary-groups-are-simple-mod-centre`, `Z(EL_N(R_∂)) ⊆ k^x I_N` for `N >= 3`, so step 3
   applies to `S_∂`.
