---
rg: 2
id: free-minimal-sft-el-sofic-via-subshift-marked-limits
kind: route
title: Soficity of elementary groups over a free minimal Z^2-SFT through marked limits of groups over other subshifts (dead)
target: free-minimal-subshift-elementary-groups-are-sofic
requires: []
artifacts:
  - research/artifacts/sk-fp-sofic-b-z2-soficity-map-2026-09-13.md
---

**DEAD.** It is invalidated by `subshift-algebra-groups-embed-in-marked-groups`.

**The idea.** Approximate `S_n(Ω) = EL_n(LC(Ω,F_q) ⋊ Z^2)/Z` in the space of marked groups by the groups
`EL_n(LC(Y_k,F_q) ⋊ Z^2)`, or their quotients by constant scalars, over subshifts `Y_k ≠ Ω` whose groups are
sofic or LEF. This would copy the `d = 1` mechanism, where periodic words give finite subshifts with the same
small words.

**Where it dies.**
- The map `Y ↦` marked group is a homeomorphism onto its image.
- A minimal subshift of finite type is an isolated point of the space of subshifts.
- So no sequence of groups over subshifts `Y_k ≠ Ω` converges to `S_n(Ω)`.
- Any finite or sofic model of `S_n(Ω)` must therefore come from outside the family of subshift algebras, for
  example from periodic quantum tilings.
