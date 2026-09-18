---
rg: 2
id: deligne-lattice-bh-via-lagrangian-brin-thompson-group
kind: route
title: Deligne's lattice satisfies Boone-Higman if the commutator subgroup of the Lagrangian Brin-Thompson group is finitely presented
target: deligne-lattice-satisfies-boone-higman
requires:
  - deligne-lattice-in-fg-simple-lagrangian-brin-thompson-group
  - lagrangian-brin-thompson-group-is-finitely-presented
---

**Conditional route.** It rests on the OPEN claim
`lagrangian-brin-thompson-group-is-finitely-presented`, which asks for finite
presentation of `D(2V_Λ(n))` at `n = 2`. At any `n ≥ 2` it gives the target's "any
`n ≥ 2` behaves the same" reading.

1. By `deligne-lattice-in-fg-simple-lagrangian-brin-thompson-group`, Deligne's lattice
   `Γ̃_n` embeds in `D(2V_Λ(n))`, and that group is simple. This holds for every
   `n ≥ 2`, including `n = 2`, where the central involution needs the factor
   `F_2 = F_3^4 ∖ {0}`.
2. If `D(2V_Λ(n))` is finitely presented, then `Γ̃_n` embeds in a finitely presented
   simple group. That is the target. ∎

**Comparison with the other conditional routes.**
- `deligne-bh-via-rational-projective-full-group` needs finite presentation of a
  rational projective group `𝒯_{m+2}`, *and* the open class-death claim
  `deligne-class-dies-on-some-rational-projective-host`.
- `lagrangian-thompson-group-is-finitely-presented` needs, for the odometer host `V_Λ^τ`,
  finite presentation and simplicity and containment.
- This route needs finite presentation only. The class death, the simplicity and the
  containment are already established.
