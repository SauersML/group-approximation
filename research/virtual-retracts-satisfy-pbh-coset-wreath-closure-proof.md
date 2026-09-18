---
rg: 2
id: virtual-retracts-satisfy-pbh-coset-wreath-closure-proof
kind: route
title: Retract case in the finite-index subgroup, then the finite-index inheritance; the classes come from Hall, Wilton, and commensurability
target: virtual-retracts-satisfy-pbh-coset-wreath-closure
requires:
  - pbh-coset-wreath-subgroups-closure-properties
  - pbh-coset-wreaths-iff-identity-edge-hnns
  - boone-higman-type-a-class-closed-under-finite-extensions
  - limit-groups-over-hyperbolic-groups-satisfy-boone-higman
  - char-zero-linear-groups-satisfy-permutational-boone-higman
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

Direct proof (2026-09-18, lane bh-openq-papers). Not independently reviewed.

**1. Virtual retracts.**
- `K ∈ B_A`, as a subgroup of `G`.
- `C` is a retract of `K`, so `C ∈ CR(K)` by case 3 of `pbh-coset-wreaths-iff-identity-edge-hnns`.
- By part 2 of `pbh-coset-wreath-subgroups-closure-properties`, `C ∈ CR(G)`.
- The listed groups:
  - `A ≀_{G/C} G` and `G *_C (C × K')` come from conditions (b) and (c) of the equivalence.
  - *The double.* In `H = G *_C (C × ⟨t⟩)`, which is (c) with `K' = Z`, the subgroup
    `⟨G, tGt^(-1)⟩` is `G *_C tGt^(-1) ≅ G *_C G`. By Britton's lemma, an alternating product
    `g_0 (t g_1 t^(-1)) g_2 ⋯` with all `g_i ∉ C` (except possibly the ends) is a reduced HNN
    word, hence nontrivial. This is the argument of step 4 of
    `double-of-psl2-z-half-along-psl2-z-proof`.
- The simple envelopes come from `type-a-action-gives-boone-higman-for-subgroups`.

**2. Property (LR).**
- Every finitely generated subgroup of `G` is a virtual retract, so lies in `CR(G)` by item 1.
- For `G' ⊇ G` with `[G' : G] < ∞`, `G' ∈ B_A`
  (`boone-higman-type-a-class-closed-under-finite-extensions`).
- The Commensurability consequence of `pbh-coset-wreath-subgroups-closure-properties` gives
  the claim for `G'`.
  - It uses parts 1 and 2 there, and the fact that `C ∩ G` has finite index in `C`.
  - So `C ∩ G` is finitely generated when `C` is.

**3. The classes.**
- **Free groups.** They are in `B_A` (they embed in `V`). Marshall Hall's theorem gives (LR).
- **Limit groups.**
  - *In `B_A`:* by `limit-groups-over-hyperbolic-groups-satisfy-boone-higman` with `Γ` free.
    Surface groups and all finitely generated Fuchsian groups are also in `B_A` directly:
    they are finitely generated subgroups of `PSL_2(R)`, which is linear in characteristic 0
    through its adjoint representation (`char-zero-linear-groups-satisfy-permutational-boone-higman`).
  - *(LR):* Wilton, arXiv:math/0605546, abstract (read 2026-09-18): "A celebrated theorem of
    Marshall Hall Jr. implies that finitely generated free groups are subgroup separable and
    that all of their finitely generated subgroups are retracts of finite-index subgroups.
    ... we prove that all limit groups share these two properties."
- **Virtually free groups and Fuchsian groups.**
  - A finitely generated virtually free group contains a free group of finite rank with
    finite index.
  - A finitely generated Fuchsian group is virtually free if it is not cocompact, and
    virtually a closed orientable surface group of genus `≥ 2` if it is cocompact and not
    elementary (Selberg's lemma, cited). Elementary Fuchsian groups are virtually abelian,
    and every subgroup of `Z^n` is a virtual retract.
  - Each such group is in `B_A`: it is a finite-index overgroup of a free or surface group
    (`boone-higman-type-a-class-closed-under-finite-extensions`), or a finitely generated
    linear group in characteristic 0.
  - Apply item 2 in each case. ∎

**Scope check.** For `Z^n`: a subgroup `D ≤ Z^n` has finite index in its saturation `S`, which
is a direct summand `Z^n = S ⊕ T`. Then `D ⊕ T` has finite index and retracts onto `D`.
