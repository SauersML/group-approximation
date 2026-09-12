---
rg: 2
id: stably-finite-simple-hosts-are-binary-power-surjunctive
kind: claim
title: A finitely generated simple group with stably finite binary group algebra is surjunctive over binary-power alphabets
distinct_from:
  stable-finiteness-forces-binary-surjunctivity: that is the same implication for every group; this restricts it to finitely generated simple hosts, where the formalizability input is not refuted.
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
---

**OPEN.** Let `S` be a finitely generated simple group whose group algebra `F_2[S]` is stably finite.
Then every injective cellular automaton on `(F_2^n)^S` is surjective, for every `n >= 1`.

**Place in the graph.**
- **From formalizability.** It follows from `binary-left-inverse-pairs-over-fg-simple-groups-are-formalizable`
  through `simple-host-formalization-reduces-surjunctivity-to-kaplansky`.
- **Every group.** Together with stable finiteness of `F_2[S]` for every finitely generated simple Kazhdan
  group, and `gottschalk-reduces-to-fg-simple-kazhdan-groups`, it gives
  `every-group-is-surjunctive-over-binary-power-alphabets`.
- **Leavitt units.** For `L_(F_2)(1,2)^x` it would turn stable finiteness of the group algebra into
  surjunctivity of that unit group over binary-power alphabets.
