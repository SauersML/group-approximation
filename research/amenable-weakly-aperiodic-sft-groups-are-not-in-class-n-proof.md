---
rg: 2
id: amenable-weakly-aperiodic-sft-groups-are-not-in-class-n-proof
kind: route
title: Amenability gives an invariant measure on every nonempty SFT; the class-𝔑 periodic point theorem finishes
target: amenable-weakly-aperiodic-sft-groups-are-not-in-class-n
requires: [class-n-groups-have-periodic-points-in-measured-sfts]
artifacts:
  - research/artifacts/un-class-n-conjecture-2026-09-13-part1.md
---

On an amenable group every nonempty compact invariant set `Y` carries an invariant probability measure: take a
Følner sequence `F_n`, a point `y ∈ Y`, and a weak* limit of `|F_n|^(-1) Σ_(g ∈ F_n) δ_(g·y)`, which is supported on
`Y` and invariant because `|gF_n Δ F_n| / |F_n| -> 0`. If `Γ ∈ 𝔑`, the SFT `Y` then has a finite orbit by
`class-n-groups-have-periodic-points-in-measured-sfts`. Contrapositive: a weakly aperiodic SFT rules out `Γ ∈ 𝔑`.
Artifact part 1, Corollary N2.
