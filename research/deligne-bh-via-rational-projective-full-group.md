---
rg: 2
id: deligne-bh-via-rational-projective-full-group
kind: route
title: If Deligne's class dies over some rational projective full group T_m and T_(m+2) is finitely presented, Deligne's lattice satisfies Boone-Higman
target: deligne-lattice-satisfies-boone-higman
requires:
  - deligne-class-dies-on-some-rational-projective-host
  - central-extension-shear-lift-into-rational-projective-groups
  - rational-projective-full-groups-are-finitely-presented
  - closed-mcg-embeds-in-rational-projective-full-group
  - fp-clopen-transitive-full-cantor-groups-have-type-a-actions
---

Let `n`, `m` and `j : Sp_{2n}(Z) ↪ 𝒯_m` be as in
`deligne-class-dies-on-some-rational-projective-host`, so Deligne's class dies on the
action groupoid.

1. By `central-extension-shear-lift-into-rational-projective-groups`, Deligne's
   lattice `Γ̃` embeds in `𝒯_{m+2}`. Its centre acts by an integral shear.
2. `𝒯_{m+2}` is full and clopen transitive on `Ŝ_{m+2}`
   (`closed-mcg-embeds-in-rational-projective-full-group`, item 1, which holds for
   every `m`).
3. If `𝒯_{m+2}` is finitely presented (`rational-projective-full-groups-are-finitely-presented`,
   needed at `m + 2`), then `fp-clopen-transitive-full-cantor-groups-have-type-a-actions`
   gives it a type (A) action. Every subgroup, in particular `Γ̃`, then embeds in a
   finitely presented simple group. ∎

The route targets the instance `n` of the first premise. The target node is stated
for `n = 2`, noting that "any `n >= 2` behaves the same". It shares its finiteness
premise with `closed-mcg-bh-via-rational-projective-full-group`.
