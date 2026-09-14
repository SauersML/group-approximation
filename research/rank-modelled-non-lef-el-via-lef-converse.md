---
rg: 2
id: rank-modelled-non-lef-el-via-lef-converse
kind: route
title: A free minimal subflow of the Abels--Pruefer group gives a rank-modelled simple algebra whose rank-four Kazhdan elementary group is not LEF, through the LEF converse
target: rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group
requires:
  - amenable-minimal-crossed-products-have-faithful-rank-models
  - finitely-presented-lef-groups-are-residually-finite
  - gjs-countable-groups-have-free-minimal-subflows
  - abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center
  - crossed-products-are-transformation-steinberg-algebras
  - steinberg-algebra-simple-iff-minimal-effective
  - elementary-groups-over-fg-rings-have-property-t
  - lef-elementary-groups-force-lef-rings
  - simple-lef-rings-are-exactly-matricial
  - exactly-matricial-rings-have-lef-general-linear-groups
artifacts:
  - research/artifacts/un-sofic-not-lef-2026-09-13-part1.md
  - research/artifacts/sk-subgroups-full-group-inside-2026-09-13-part2.md
---

This route is a repair (lane sk-subgroups, 2026-09-13) of `rank-modelled-non-lef-el-via-amenable-non-rf-subflow`.
- That route's step 3 embedded `Γ_p` in `EL_N(R)` through `diag(u_γ, u_γ^(-1), 1)`, which is not a homomorphism on the
  nonabelian `Γ_p` (`whitehead-diagonal-map-is-not-multiplicative`).
- Steps 1–2 are unchanged, and step 3 now goes through the ring.

1. **The ring.** Let `k = F_q`, and `R = LC(X, F_q) ⋊ Γ_p` for a free minimal subflow `X` of the Abels–Prüfer group (Gao–Jackson–Seward).
   - `R` is countable, finitely generated and infinite.
   - `R` is simple: it is the Steinberg algebra of a minimal effective groupoid.
   - It has a unital rank model over `F_q` (Theorem F), since `Γ_p` is amenable.
2. **(T).** `EL_N(R)` is Kazhdan for `N >= 3` (Ershov–Jaikin-Zapirain).
3. **Not LEF, `N = 4`.**
   - `Γ_p` is finitely presented and not residually finite, since its central `c_p` dies in every finite quotient. So it is not LEF.
   - If `EL_4(R)` were LEF, then `R` would be a LEF ring (`lef-elementary-groups-force-lef-rings`).
   - Being countable and simple, `R` would then embed unitally in a matrix ultraproduct over finite fields
     (`simple-lef-rings-are-exactly-matricial`).
   - Then `R^× = GL_1(R)` would be LEF (`exactly-matricial-rings-have-lef-general-linear-groups`).
   - `γ ↦ u_γ` embeds `Γ_p` in `R^×`, and the representation is unique, so `Γ_p` would be LEF. This is a contradiction.
   - So `EL_4(R)` is Kazhdan and not LEF, which realizes the claim with `N = 4`.

**Review (sk-verify-3, 2026-09-13): PASS.** The existential target is realized at `N = 4` through the LEF converse. See `research/artifacts/sk-review-3-2026-09-13-part6.md` §B2.
