---
rg: 2
id: cleary-golden-ratio-group-does-not-embed-in-thompson-f
kind: claim
title: Cleary's golden-ratio Thompson group F_τ is not a subgroup of F
distinct_from:
  stein-group-f23-does-not-embed-in-thompson-v: that is the Stein group F_{2,3}, whose germ group at the endpoints is Z^2 and which is excluded from V; this is F_τ, with cyclic germ group, and only excluded from F
  wreath-z-by-z2-does-not-embed-in-thompson-f: that is a metabelian group excluded from F by an in-repo bump argument; this is the irrational-slope Thompson group, excluded from F by Hyde–Moore F-obstructions
---

Let `τ = (√5 − 1)/2`, and let `F_τ` be Cleary's irrational-slope Thompson group, the
Bieri–Strebel group `F([0,1]; Z[τ], ⟨τ⟩)`. Its elements are the orientation-preserving
piecewise-linear homeomorphisms of `[0,1]` with finitely many breakpoints in `Z[τ]` and
slopes in `τ^Z`. `F_τ` is isomorphic to no subgroup of Thompson's group `F`.

Imported from Hyde–Moore (Groups Geom. Dyn. 17 (2023), arXiv:2103.14911): route
`cleary-golden-ratio-group-not-in-f-citation`.

`F_τ` is a subgroup of `PL_+([0,1])`, so it is bi-orderable and has no non-abelian free
subgroup. So `F_τ` would be a negative answer to the reposed Zaremsky Problem 2.15 if it
embedded in `V`. See `cleary-golden-ratio-group-embeds-in-thompson-v`.
