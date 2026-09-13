---
rg: 2
id: f-infinity-hosts-via-rp-fp-infinity-hosts
kind: route
title: "Recursively presented FP_infinity hosts give F_infinity hosts for all finitely presented groups"
target: every-finitely-presented-group-embeds-in-an-f-infinity-group
requires:
  - every-fg-rp-group-embeds-in-an-rp-fp-infinity-group
  - fournier-facio-zaremsky-rp-fp-n-hosts-give-f-n-hosts
---

Apply Theorem A of Fournier-Facio--Zaremsky with `n = ∞`. Its hypothesis is
the first required claim, and its conclusion is that every finitely presented
group embeds into a group of type `F_∞`, which is the target.
