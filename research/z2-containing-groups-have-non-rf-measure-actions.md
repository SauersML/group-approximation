---
rg: 2
id: z2-containing-groups-have-non-rf-measure-actions
kind: claim
title: Every group containing Z^2 has a Cantor action with a full-support invariant measure that is not residually finite, minimal and free when the group is Z^2 × Λ
distinct_from:
  sfts-without-finite-orbits-are-not-residually-finite-actions: that proves subshifts inside SFTs without finite orbits are not RF; this uses it at Labbé's shift to separate invariant measures from finite models for every group containing Z^2.
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).**
1. Labbé's Wang shift `Ω_U` is a minimal free Cantor `Z^2`-system with an invariant probability measure of full
   support that is not residually finite (Kerr–Nowak).
2. If `Γ` contains `Z^2`, some continuous `Γ`-action on a Cantor space with a full-support invariant probability
   measure is not residually finite. So `Γ ∉ 𝔑` (`measure-rf-property-passes-to-subgroups`).
3. If `Γ = Z^2 × Λ` with `Λ` countable, there is a **minimal free** Cantor `Γ`-system with an invariant
   probability measure that is not residually finite.

So the dynamical input behind the UN flagship (invariant measure ⟹ genuine finite models) is special to groups
without `Z^2`: it holds for virtually free groups (`virtually-free-group-measure-actions-are-rf`) and fails here.
The witness of item 2 for groups like `SL_3(Z)` (co-induction) is not minimal; whether a minimal topologically free
witness exists there is recorded in `measure-rf-class-is-exactly-virtually-free-groups`.

Route: `z2-containing-groups-have-non-rf-measure-actions-proof`.
