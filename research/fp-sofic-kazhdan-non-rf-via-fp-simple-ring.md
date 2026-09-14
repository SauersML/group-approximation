---
rg: 2
id: fp-sofic-kazhdan-non-rf-via-fp-simple-ring
kind: route
title: A finitely presented simple sofic elementary group over a simple ring answers Open problem 6.1
target: fp-sofic-kazhdan-group-not-residually-finite
requires:
  - sofic-fp-simple-kazhdan-group-from-fp-simple-ring
---

The required claim gives `S = EL_n(R)/Z(EL_n(R))` finitely presented, simple and sofic, for a
finitely presented infinite simple unital ring `R` and `n >= 3`.
- `S` is infinite, since it contains the image of `e_12(R)`.
- `S` is Kazhdan, since `R` is finitely generated (Ershov--Jaikin-Zapirain), as that claim records.
- An infinite simple group is not residually finite.

So `S` witnesses the target.
