---
rg: 2
id: bestvina-brady-groups-have-connected-rips-complexes
kind: claim
title: Bestvina-Brady groups of type F_n have (n-1)-connected Rips complexes
artifacts:
  - research/artifacts/zp-cube-level-set-rips-2026-09-13.md
---

Let `L` be a finite flag complex with 1-skeleton `Γ`, let `A_Γ` be the
right-angled Artin group, `φ: A_Γ → Z` the homomorphism sending every generator
to `1`, and `H_L = ker φ` the Bestvina–Brady group. Put

`T = {∏_{v∈α} v · ∏_{w∈β} w^{-1} : α, β disjoint vertex sets of one simplex of L, |α| = |β| >= 1}`

(the factors commute). If `L` is (n−1)-connected (`n >= 1`), then `T` generates
`H_L` and the Rips complex `R_1(H_L, T) = Flag(Cay(H_L, T))` is (n−1)-connected.

For `n >= 2`, `H_L` is of type `F_n` iff `L` is (n−1)-connected. This follows
from Bestvina–Brady's Main Theorem (`FP_n` iff `L` is homologically
(n−1)-connected; finitely presented iff `L` is simply connected) and Hurewicz.
So **every Bestvina–Brady group of type `F_n` has an (n−1)-connected Rips
complex.**

Taking `L` to be the octahedral `n`-sphere gives `A_Γ = F_2^{n+1}`, and `H_L`
is the Bieri–Stallings group, of type `F_n` but not `F_{n+1}`. So for every `n`
there are groups of type `F_n` not `F_{n+1}` with (n−1)-connected Rips
complexes, and the gap between `F_n` and `F_{n+1}` is not by itself an
obstruction in Zaremsky Problem 4.4.

Proof: `bestvina-brady-groups-have-connected-rips-complexes-proof`. Unreviewed.
