---
rg: 2
id: e-type-artin-groups-satisfy-permutational-boone-higman
kind: claim
title: The Artin groups of types E_6, E_7, E_8 embed in groups with type (A) actions
distinct_from:
  spherical-artin-boone-higman-reduces-to-e6-e7-e8: that is the established conditional statement that this claim implies the permutational property for every spherical type; this is the open hypothesis itself.
  spherical-artin-groups-satisfy-boone-higman: that is Boone--Higman for all spherical types; this is the stronger permutational property for the three E types only.
  aut-free-groups-satisfy-permutational-boone-higman: that imports the Aut(F_n) theorem and the Artin types it reaches; this asks for the permutational property for E_6, E_7, E_8, which that theorem is not known to reach.
artifacts:
  - research/artifacts/bh-artin-groups-2026-09-12.md
---

**OPEN.** Each of `A(E_6)`, `A(E_7)` and `A(E_8)` embeds in a finitely presented
group admitting an action of type (A). In the language of BFFHZ, each satisfies
the permutational Boone--Higman property.

By `spherical-artin-boone-higman-reduces-to-e6-e7-e8`, this gives the property
for every spherical-type Artin group.

## Attempts

1. **Through Aut(F_n) via geometric monodromy.** *Dies as it stands.* The
   Perron--Vannier representation is faithful only for types A and D (Paris,
   arXiv:0711.2372, §7.1). No other faithful embedding of an E-type Artin group
   in a mapping class group of a surface with boundary or punctures is recorded
   in the sources read.
2. **Through linearity.** *Gives the plain form only* (2026-09-12).
   - **Envelopes.** `spherical-artin-groups-are-linear-over-q-x-y` places these
     groups over `Q(x,y)`. The root `char-zero-linear-groups-satisfy-boone-higman`,
     now established, gives simple envelopes, so
     `spherical-artin-groups-satisfy-boone-higman` holds.
   - **Trust.** That rests on `polynomial-linear-groups-satisfy-boone-higman`,
     whose review is pending (lane `bh-poly-linear-review`).
   - **Why this claim stays open.** Whether those envelopes come from type (A)
     actions is not asked there. The E-reduction needs the permutational form,
     because only that form is known to be closed under direct products.
