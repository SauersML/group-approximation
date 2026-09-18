---
rg: 2
id: kazhdan-subgroups-of-nv-fibration-stabilizers-are-finite
kind: claim
title: Every Kazhdan subgroup of nV that maps the fibres of a coordinate projection C^n -> C^I onto fibres, or of a conjugate of that stabilizer, is finite
distinct_from:
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that asks finiteness for all Kazhdan subgroups of nV; this settles it for subgroups preserving a coordinate fibration up to conjugacy, so an infinite Kazhdan subgroup must virtually preserve no such fibration.
  thompson-v-has-haagerup-property: that is the case n = 1 through a proper affine action; this inducts on n through the base map to |I|V and the locally constant fibre maps into |J|V, using the n = 1 case as the base.
  fw-subgroups-of-eventually-similar-groups-virtually-embed: that virtually embeds FW subgroups of one-shift similarity groups through commensurated cones; this uses no commensurated set, only the product structure of a preserved fibration.
artifacts:
  - research/artifacts/kazhdan-nv-displacement-gap-2026-09-17.md
---

**ESTABLISHED** by `nv-fibration-stabilizer-kazhdan-finite-proof` (agent-verified only,
no referee pass as of 2026-09-17).

## Statement

For `n >= 2`, nonempty `I ⊊ {1,...,n}` with complement `J`, let `Stab_I <= nV` be the
elements `g` with `g({a} x C^J) = {v(a)} x C^J` for a bijection `v` of `C^I`. Every
Kazhdan subgroup of `h Stab_I h^{-1}` (`h ∈ nV`) is finite.

## Consequence for the target

An infinite Kazhdan `K <= nV` virtually preserves no `nV`-image of a coordinate fibration.
The decomposition "(T) forces a virtually preserved coordinate fibration" would prove
`kazhdan-subgroups-of-brin-thompson-groups-are-finite`, hence
`minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures`; that prerequisite is
not claimed and can fail on its own. Details: artifact Section D.
