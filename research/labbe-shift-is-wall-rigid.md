---
rg: 2
id: labbe-shift-is-wall-rigid
kind: claim
title: Labbé's shift admits no wall certificate at large scale, so every first-order operator family commutes and its local tiling algebra has an idempotent commutator ideal
distinct_from:
  labbe-wang-shift-crossed-product-is-finitely-presented: that is full quantum rigidity (finite presentation of the crossed product); this is its first-order part, which holds, reducing the open question to vanishing of an idempotent commutator ideal.
  sft-wall-rigidity-iff-idempotent-commutator-ideal: that is the general equivalence for SFTs; this verifies wall rigidity for Labbé's shift from its Markov partition geometry.
artifacts:
  - research/artifacts/labbe-shift-wall-rigidity-2026-09-13.md
---

**ESTABLISHED (unreviewed).** There is `D_0` such that for all `D >= D_0` and all tilings
`T_1, T_2 ∈ Ω_U`, the difference set `{n : T_1(n) != T_2(n)}` is `2D`-connected. So no two tilings agree on
a thick wall separating two regions where they differ.

**Consequences** (by `sft-wall-rigidity-iff-idempotent-commutator-ideal`), for `D >= D_0` and every field:
- **First order.** The local tiling algebra `C_D` of `Ω_U` has `J_D = J_D^2`. Every operator family on `k^2`,
  and every finitely filtered family with commuting quotients, commutes.
- **Finite dimensions.** Over an algebraically closed field, a noncommuting finite-dimensional family, or a
  periodic quantum tiling, has a composition factor of dimension `>= 3`.
- **Reduction.** `labbe-wang-shift-crossed-product-is-finitely-presented` holds iff `J_D = 0` for some `D`.

**Mechanism.** Tilings are codings of `x + φ^(-2) n` through a polygonal partition whose boundary segments
point in four directions: `(1,0)`, `(0,1)`, `(1,-1)`, `(1,-φ)`.
- **Distinct torus points.** Two tilings with nearby torus points differ along a network of lattice lines and
  golden strips in at least two directions, which cross. Far-apart torus points differ on a syndetic set.
- **Same fibre.** Tilings over the same torus point differ on full fault lines, and finite clusters are ruled
  out by minimality and zero entropy.
- **Singular tilings.** These are limits of generic ones, and local paths in the network pass to the limit.

Route: `labbe-shift-is-wall-rigid-proof`.
