---
rg: 2
id: cusp-extensions-of-torsion-free-hyperbolic-groups-satisfy-pbh
kind: claim
title: For torsion-free hyperbolic H, h ≠ 1 and any finitely generated P in the permutational class, the relatively hyperbolic group H *_{E(h)} (E(h) x P) embeds in a finitely presented simple group
distinct_from:
  hyperbolic-groups-satisfy-boone-higman: that is Belk--Bleak--Matucci--Zaremsky for hyperbolic inputs; these amalgams are not hyperbolic (they contain E(h) × P), and they are relatively hyperbolic with peripheral subgroup E(h) × P.
  rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh: that is the OPEN permanence statement for all relatively hyperbolic groups with Boone--Higman peripherals; this settles the family of cusp extensions with peripherals in the permutational class.
  finitely-generated-linear-groups-satisfy-boone-higman: that covers linear inputs; no linearity or residual finiteness of H or P is assumed here.
  pbh-class-closed-under-centralizer-amalgams: that is the general closure statement; this applies it to hyperbolic groups and records the relatively hyperbolic structure.
---

**ESTABLISHED** by `cusp-extensions-hyperbolic-pbh-proof` (lane proof, not reviewed;
no priority claimed).

## Statement

Let `H` be a torsion-free hyperbolic group, `h ∈ H \ {1}`, `E(h)` its maximal
elementary subgroup (infinite cyclic, and equal to the centralizer `C_H(h)`), and
`P` a finitely generated group in `B_A`. Put `Γ = H *_{E(h)} (E(h) × P)`.

1. `Γ ∈ B_A`. So `Γ` embeds in a finitely presented simple group.
2. `Γ` is hyperbolic relative to `{E(h) × P}` (for finitely generated `P`), and
   `E(h) × P ∈ B_A`.
3. Iterating (with `h_i` in the hyperbolic vertex group each time) stays in `B_A`,
   by `pbh-class-closed-under-centralizer-amalgams`, but item 2 is claimed only
   for one step.

## Examples

`P = Z` gives `H *_{<r>} Z^2` (`r` a root of `h`), a toral relatively hyperbolic
group. `P = V` (Thompson's group) or `P` a finitely presented simple Kazhdan group
in `B_A` gives relatively hyperbolic groups with non-linear, non-residually-finite
peripheral subgroups. None of these is hyperbolic, and none is linear when `P` is not.
