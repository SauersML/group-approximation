---
rg: 2
id: class-n-groups-have-periodic-points-in-measured-sfts
kind: claim
title: Over a group in the measure class 𝔑, every subshift of finite type that carries an invariant probability measure has a finite orbit
distinct_from:
  sfts-without-finite-orbits-are-not-residually-finite-actions: that shows subshifts inside an SFT without finite orbits are not RF; this turns it into a necessary condition on the acting group, quantifying over all measured SFTs.
artifacts:
  - research/artifacts/un-class-n-conjecture-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** If `Γ ∈ 𝔑` and `Y ⊆ A^Γ` is an SFT carrying an invariant Borel probability
measure, then `Y` contains a configuration with finite `Γ`-orbit.

So a group is **not** in `𝔑` as soon as it has a *measured weakly aperiodic* SFT: an SFT with an invariant
probability measure and no finite orbit. For non-amenable groups both properties must be arranged at once. Free
groups have weakly aperiodic SFTs (Piantadosi, recalled) but lie in `𝔑`, so their weakly aperiodic SFTs carry no
invariant measure.

Route: `class-n-groups-have-periodic-points-in-measured-sfts-proof`.
