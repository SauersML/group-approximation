---
rg: 2
id: f-infinity-fcd-type-f-from-retract-closure
kind: route
title: "An F_infinity group of finite cd is a retract of the type F group G x Z"
target: f-infinity-groups-of-finite-cd-are-of-type-f
requires: [retracts-of-type-f-groups-are-of-type-f, g-times-z-type-f-iff-g-f-infinity-with-finite-cd]
artifacts:
  - research/artifacts/zaremsky-1-21-fibering-and-retracts-2026-09-16.md
---

Let `G` be of type `F_∞` with `cd G < ∞`.

1. By `g-times-z-type-f-iff-g-f-infinity-with-finite-cd`, (2)⇒(1), the group
   `Γ = G × Z` is of type F.
2. The maps `i: G → Γ`, `g ↦ (g,0)`, and the projection `r: Γ → G` satisfy
   `r∘i = id_G`, so `G` is a retract of `Γ`.
3. By `retracts-of-type-f-groups-are-of-type-f`, `G` is of type F. QED

Together with `retract-closure-from-f-infinity-fcd-type-f`, this makes the
retract closure property and the hole equivalent.
