---
rg: 2
id: automaton-groups-bh-via-lift-presented-overgroups
kind: route
title: Embed every automaton group in an automaton group whose relator kernel is a finitely generated lift ideal, then apply the lift-ideal Boone–Higman theorem
target: automaton-groups-satisfy-boone-higman
requires:
  - automaton-groups-embed-in-lift-presented-automaton-groups
  - lift-presented-automaton-groups-satisfy-boone-higman
---

Immediate: if `G <= G'` with `G'` an automaton group whose relator kernel is a finitely generated lift
ideal, then `G' ` embeds in a finitely presented simple group by
`lift-presented-automaton-groups-satisfy-boone-higman`, and so does `G`. The alphabet of `G'` may
differ from that of `G`. Only the first premise is open.
