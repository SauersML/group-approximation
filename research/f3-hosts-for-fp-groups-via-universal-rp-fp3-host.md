---
rg: 2
id: f3-hosts-for-fp-groups-via-universal-rp-fp3-host
kind: route
title: "A recursively presented FP_3 host of a universal finitely presented group gives F_3 hosts for all finitely presented groups"
target: every-finitely-presented-group-embeds-in-an-f3-group
requires:
  - ffz-rp-fpn-embedding-gives-fp-fn-embedding
  - universal-fp-group-embeds-in-an-rp-fp3-group
---

Let `U ≤ H` with `H` recursively presented and of type `FP_3`, as the second
required claim provides. Let `K` be any finitely generated recursively
presented group. By the Higman embedding theorem `K` embeds in a finitely
presented group, and that group embeds in `U` by universality. So `K` embeds
in the recursively presented group `H` of type `FP_3`.

This is the hypothesis of Theorem A of Fournier-Facio–Zaremsky (the first
required claim) at `n = 3`. Its conclusion is that every finitely presented
group embeds in a group of type `F_3`, which is the target.
