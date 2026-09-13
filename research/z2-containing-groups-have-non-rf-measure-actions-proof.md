---
rg: 2
id: z2-containing-groups-have-non-rf-measure-actions-proof
kind: route
title: Labbé's minimal aperiodic Wang shift carries an invariant measure but no finite models, and co-induction or products carry that to bigger groups
target: z2-containing-groups-have-non-rf-measure-actions
requires:
  - minimal-aperiodic-wang-shift-exists
  - sfts-without-finite-orbits-are-not-residually-finite-actions
  - measure-rf-property-passes-to-subgroups
  - elek-free-minimal-cantor-actions-with-invariant-measures
  - extensions-of-aperiodic-sfts-are-not-residually-finite-actions
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part1.md
---

Artifact part 1, §4, Theorem Z.
1. `Ω_U` is a minimal aperiodic SFT (`minimal-aperiodic-wang-shift-exists`): infinite and minimal, hence perfect,
   a Cantor space, and free. `Z^2` is amenable, so an invariant measure exists, of full support by minimality. No
   finite orbit exists (a finite orbit gives a nonzero period), so `Ω_U` is not RF
   (`sfts-without-finite-orbits-are-not-residually-finite-actions`, item 1).
2. `Z^2 ∉ 𝔑` by 1, and `𝔑` is closed under subgroups (`measure-rf-property-passes-to-subgroups`), so no group
   containing `Z^2` is in `𝔑`.
3. For infinite `Λ` take a free minimal `Λ ↷ C` with an invariant measure `ν`
   (`elek-free-minimal-cantor-actions-with-invariant-measures`); for finite `Λ` take `C = Λ` by translation.
   - The product action of `Z^2 × Λ` on `Ω_U × C` is minimal, free, and preserves `μ × ν`.
   - If it were RF, its restriction to `Z^2 × {e}` would be RF (restrict the finite actions).
   - The projection onto `Ω_U` is a `Z^2`-factor map onto a perfect space, so `Ω_U` would be RF
     (`extensions-of-aperiodic-sfts-are-not-residually-finite-actions`, item 1), contradicting 1.
