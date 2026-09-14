---
rg: 2
id: lot-group-free-splittings-force-torsion
kind: claim
title: If a LOT group splits as a free product H * Z with H nontrivial, then H is perfect and has torsion
distinct_from:
  balanced-kervaire-failure-refutes-stable-ac-or-lot-torsion-free: that shows a free splitting H * Z of a LOT group is a Kervaire killing failure over H; this adds Klyachko's theorem to conclude that H must have torsion, so torsion-freeness of LOT groups already forbids free splittings.
  lot-groups-are-torsion-free: that is the open statement that no LOT group has torsion; this shows that it implies free indecomposability of LOT groups other than Z.
artifacts:
  - research/artifacts/hl-lot-torsion-2026-09-14.md
---

**ESTABLISHED** through `lot-group-free-splittings-torsion-proof`. Unreviewed. No novelty is claimed;
this composes the converse direction of
`balanced-kervaire-failure-refutes-stable-ac-or-lot-torsion-free` with Klyachko's theorem.

**Claim.** Let `Γ` be a LOT, and suppose `G(Γ) ≅ H * Z` with `H ≠ 1`. Then `H_1(H) = 0`, and `H` contains a
nontrivial element of finite order. In particular `G(Γ)` has torsion, it is not locally indicable, and
`K(Γ)` is not aspherical.

**Consequences.**
- In item (iv) of the consequence list of
  `balanced-kervaire-failure-refutes-stable-ac-or-lot-torsion-free` ("no LOT group is a free product
  `H * Z` with `H != 1`"), (iv) follows from (i) (`lot-groups-are-torsion-free`).
- The LOT groups of `crossing-pair-two-cycle-lot-groups-are-locally-indicable` never split this way.
- A free splitting of a LOT group would refute Kervaire--Laudenbach over a group with torsion and give a
  ribbon disc complement spine that is not aspherical.
