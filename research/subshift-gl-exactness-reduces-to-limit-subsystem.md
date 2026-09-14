---
rg: 2
id: subshift-gl-exactness-reduces-to-limit-subsystem
kind: claim
title: If every orbit outside a closed invariant subsystem Z of a subshift Y has both limit sets in Z, finitely generated subgroups of GL_m over Y are exact whenever their images over Z are
distinct_from:
  biasymptotic-subshift-complement-ideal-is-ultramatricial: that proves the complement ideal is ultramatricial; this uses it to reduce exactness of matrix groups over the subshift to the limit subsystem
  subshift-el-n-exactness-is-kakutani-invariant: that transfers exactness across ranks and induced systems of one minimal system; this passes from a non-minimal subshift to its limit subsystem
artifacts:
  - research/artifacts/sk-exact-banded-2026-09-14-part2.md
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `Y ⊆ A^Z` is a subshift, and `Z ⊆ Y` is closed and invariant, with `α(x) ∪ ω(x) ⊆ Z` for every `x ∈ Y∖Z`.
- `R_Y = LC(Y,F_2) ⋊ Z`. Restricting coefficients gives the surjection `ρ: R_Y → R_Z` with kernel `I_Z`.

**Theorem.** Let `m ≥ 1` and let `Γ ≤ GL_m(R_Y)` be finitely generated. If `ρ(Γ) ≤ GL_m(R_Z)` is exact, then `Γ` is exact. The kernel `Γ ∩ GL_m(R_Y, I_Z)` is locally finite.

**Corollaries.**
- **(a)** Suppose there are closed invariant subsets `Y = Y_0 ⊇ Y_1 ⊇ … ⊇ Y_d` such that every point of `Y_i∖Y_{i+1}` has both limit sets in `Y_{i+1}`, and `Y_d` is a finite union of periodic orbits. Then every finitely generated subgroup of `GL_m(R_Y)` is exact.
- **(b)** In particular, if `y` is asymptotic to periodic sequences at `+∞` and at `−∞`, every finitely generated subgroup of `GL_m` over the orbit closure of `y` is exact. This covers every finitely generated group of banded matrices over `F_2` whose coefficient functions are eventually periodic in both directions (`banded-matrix-groups-are-subshift-crossed-product-groups`).
- **(c)** So exactness of finitely generated groups of banded matrices over `F_2` is in question only through subsystems carrying recurrence. Along any such chain the obstruction is concentrated in the bottom subsystem, and when that subsystem is an infinite minimal subshift `X` it is a subgroup of `GL_m(R_X)`, whose exactness is the open node `subshift-elementary-groups-are-exact` in rank `m`.

**Proof:** `subshift-gl-exactness-reduces-to-limit-subsystem-proof`.
