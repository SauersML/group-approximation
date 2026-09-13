---
rg: 2
id: ia-n-not-fp-infinitely-often-via-outer-torelli
kind: route
title: "Infinitely many non-finitely-presented Out(F_n) Torelli groups give infinitely many non-finitely-presented IA_n"
target: ia-automorphism-groups-not-fp-for-infinitely-many-ranks
requires:
  - outer-torelli-groups-not-fp-for-infinitely-many-ranks
  - ia-n-fp-iff-outer-torelli-fp
---

`T_1` and `T_2` are trivial, so every rank where `T_n` fails to be finitely
presented has `n >= 3`. At each such rank `IA_n` also fails, by
`ia-n-fp-iff-outer-torelli-fp`.

This route and `outer-torelli-not-fp-infinitely-often-via-ia-n` form a deliberate
dependency cycle between equivalent claims; do not delete either direction.
