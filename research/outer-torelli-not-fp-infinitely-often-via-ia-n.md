---
rg: 2
id: outer-torelli-not-fp-infinitely-often-via-ia-n
kind: route
title: "Infinitely many non-finitely-presented IA_n give infinitely many non-finitely-presented Out(F_n) Torelli groups"
target: outer-torelli-groups-not-fp-for-infinitely-many-ranks
requires:
  - ia-automorphism-groups-not-fp-for-infinitely-many-ranks
  - ia-n-fp-iff-outer-torelli-fp
---

`IA_1` is trivial, so every rank where `IA_n` fails to be finitely presented has
`n >= 2`. At each such rank `T_n` also fails, by `ia-n-fp-iff-outer-torelli-fp`.

This route and `ia-n-not-fp-infinitely-often-via-outer-torelli` form a deliberate
dependency cycle between equivalent claims; do not delete either direction.
