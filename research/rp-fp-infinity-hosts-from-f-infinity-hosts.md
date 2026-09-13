---
rg: 2
id: rp-fp-infinity-hosts-from-f-infinity-hosts
kind: route
title: "F_infinity hosts of finitely presented groups are recursively presented FP_infinity hosts of recursively presented groups"
target: every-fg-rp-group-embeds-in-an-rp-fp-infinity-group
requires:
  - every-finitely-presented-group-embeds-in-an-f-infinity-group
  - mikaelian-explicit-higman-embedding
---

Let `Q` be finitely generated and recursively presented. By Higman's
embedding theorem, in the explicit form of the second required claim, `Q`
embeds in a finitely presented group `P`. By the first required claim, `P`
embeds in a group `K` of type `F_∞`. Then `K` is finitely presented, hence
recursively presented, and of type `FP_∞`, and `Q <= K`.

Together with `f-infinity-hosts-via-rp-fp-infinity-hosts` this records an
equivalence, so the dependency cycle is intended.
