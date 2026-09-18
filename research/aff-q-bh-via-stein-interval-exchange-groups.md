---
rg: 2
id: aff-q-bh-via-stein-interval-exchange-groups
kind: route
title: Aff(Q) inside a finitely presented Stein interval-exchange group would give Boone–Higman for Aff(Q) through its breakpoint-orbit type (A) action
target: aff-q-embeds-in-fp-simple-group
requires:
  - aff-q-embeds-in-a-stein-interval-exchange-group
  - interval-exchange-pl-groups-act-with-type-a-on-breakpoints
  - type-a-action-gives-boone-higman-for-subgroups
---

Deduction.
- `interval-exchange-pl-groups-act-with-type-a-on-breakpoints` gives a type (A) action of V(1; Z[1/M], ⟨p|M⟩) whenever it
  is finitely presented. Finite presentation is Stein's theorem, cited there, not re-read. A/I_P·A is finite, since it is a
  quotient of Z[1/M]/(p−1).
- `type-a-action-gives-boone-higman-for-subgroups` then embeds every subgroup of it, including Aff(Q), in a finitely
  presented simple group.
- Origin: this is the finitely generated part of the factorial-odometer radix-changing host
  (`factorial-odometer-affine-hosts-are-rational-stein-groups`).
