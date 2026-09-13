---
rg: 2
id: rank-modelled-non-lef-el-via-amenable-non-rf-subflow
kind: route
title: A free minimal subflow of a finitely presented amenable non-residually-finite group gives a rank-modelled simple algebra with non-LEF Kazhdan elementary groups
target: rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group
requires:
  - amenable-minimal-crossed-products-have-faithful-rank-models
  - crossed-product-group-embeds-in-projective-elementary-group
  - finitely-presented-lef-groups-are-residually-finite
  - gjs-countable-groups-have-free-minimal-subflows
  - abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center
  - crossed-products-are-transformation-steinberg-algebras
  - steinberg-algebra-simple-iff-minimal-effective
  - elementary-groups-over-fg-rings-have-property-t
artifacts:
  - research/artifacts/un-sofic-not-lef-2026-09-13-part1.md
---

Complete proof: artifact Section 4, Corollary M. No finite presentation of the ring and no quantum tilings are needed.

1. `k = F_q`, and `R = LC(X, F_q) ⋊ Γ_p` for a free minimal subflow `X` of the Abels–Prüfer group.
   - `R` is finitely generated and infinite.
   - `R` is simple: it is the Steinberg algebra of a minimal effective groupoid.
   - It has a unital rank model over `F_q` (Theorem F).
2. `EL_N(R)` is Kazhdan for `N >= 3` (Ershov–Jaikin-Zapirain).
3. `Γ_p` embeds in `EL_N(R)` by Whitehead's lemma. It is finitely presented and not residually finite (its central `c_p` dies
   in every finite quotient), hence not LEF. So `EL_N(R)` is not LEF.
