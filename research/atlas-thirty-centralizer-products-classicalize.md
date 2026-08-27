---
rg: 2
id: atlas-thirty-centralizer-products-classicalize
kind: claim
title: Near-membership in all thirty centralizer products forces approach to the finite classical alignment branches
refuted_by: atlas-a4-gl5-packet-collision-screen
distinct_from:
  atlas-a4-componentwise-commutant-collapse: that asks the frame to approach the commutant of two named packet-component subgroups; this asks it to approach classical A8 alignment branches.
  a4-near-context-centralizer-product-rounding: that is the established per-context rounding; this was the proposed joint packet-only upgrade.
artifacts:
  - research/artifacts/gpu-hyperlinear-attack-2026-08-19.md
  - experiments/atlas_a4_gl5_packet_screen.py
---

REFUTED by [[atlas-a4-gl5-packet-collision-screen]]: letting the second chart
move through all 9,999,360 elements of `GL_5(F_2)` produces 202 exact models
of the thirty-relation packet, none of them a classical alignment branch, so
near-membership in the thirty centralizer products does not force one.  The
corrected target, which adds the interior collision that kills all 202, is
[[atlas-centralizer-products-19243-classicalize]]; the route out of this
claim is invalidated accordingly.  Kept as the record of what was asked for,
not as an open target.

**REFUTED by `atlas-a4-gl5-packet-collision-screen`.**  The statement below
is kept as the record of the proposed packet-only endpoint, not as an open
target.

Fix `rho_k=Reg(A8) tensor I_k` and the corrected exact reference alignment
`R_k=rho_k(r_0)` from `atlas-a4-packet-centralizer-product-compiler`.  The
thirty local A4 conditions compile to the **shifted** sets

```text
D_(j,k)=C(rho_k(a_j)) R_k C(rho_k(b_j))
```

or the factor-reversed analogues.  The proposed statement was that

```text
max_j dist_2(U_k,D_(j,k)) -> 0
```

would force `U_k` to approach one of the finitely many classical packet
alignments, modulo the unavoidable global regular-chart commutant gauge.

This is false.  Embed `A8=GL4(F2)` standardly in `GL5(F2)`.  The exhaustive
screen finds **202 exact relative positions** satisfying all thirty packet
relations.  In the left-regular representation of `GL5(F2)`, both chart
restrictions are exactly `496 Reg(A8)`, so these are exact amplified
regular-margin solutions of every shifted centralizer-product constraint.
Among them, 172 have chart-intersection size `1344` or `168`, hence are not the
same `A8` chart subgroup and are not classical inner/outer packet alignments
modulo the global chart commutant.

Collision `19243` is nonidentity on all 202 solutions.  Therefore the correct
surviving theorem must include collision (or an equivalent interior condition)
**inside the joint classicalization hypothesis**.  It is recorded separately as
`atlas-centralizer-products-19243-classicalize`.
