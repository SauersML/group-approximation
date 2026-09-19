---
rg: 2
id: level-copies-are-kazhdan-and-compressed
kind: route
title: Every telescope level is its own Kazhdan-compressor pair
target: full-telescope-radical-in-mf-radical
requires: [stage-one-lamp-difference-radical]
artifacts:
  - GroupApproximation/Sofic/AscendingHNNFullTelescopeRadical.lean
---

## Why sufficient

The collapse criterion needs three things: a Kazhdan subgroup `L`, an element
`s` with `s L s^-1 <= L`, and an involutive witness centralized by the
compressed copy.  Stage one takes `L` to be the base and `s = t`.  The point is
that the level-`n` copy `Gamma_n = t^-n Gamma t^n` supplies the same package on
its own.

**Kazhdan.**  `Gamma_n` is a conjugate of the base, hence isomorphic to it.

**Compressor.**  `t^n Gamma_n t^-n = Gamma <= Gamma_n`, the last inclusion
because the levels increase.  So `s = t^n` compresses `Gamma_n`.

**Witness.**  The criterion needs a site fixed by the *compressed* copy, and
the compressed copy of `Gamma_n` is the base, which fixes the **root** coset.
So the one-site lamp at the root is an involutive compression witness for
`(Gamma_n, t^n)` -- for every `n`, with the same witness.

**Exhaustion.**  Every element of the telescope is a level element, by the
construction of the mapping telescope as a colimit of copies of `Gamma`.  So
the collapse commutators of the levels already cover every telescope translate
of the root, and conjugating transports them to every site.

Each level therefore contributes its own commutators with no reference to the
previous one: the iteration that seemed necessary is an artifact of fixing the
witness site at `t Gamma` instead of at the root.

## Priority

The mechanism is the dossier's; what is new here is the observation that the
collapse applies levelwise, which removes the induction on quotients that the
dossier's presentation suggests.
