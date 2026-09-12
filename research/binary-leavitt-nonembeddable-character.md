---
rg: 2
id: binary-leavitt-nonembeddable-character
kind: claim
title: The binary Leavitt unit group admits a non-Connes-embeddable character
distinct_from:
  binary-leavitt-full-character-simplex: That is the proved classification of all characters; this asks for an actual nonembeddable member of that simplex.
  leavitt-24k-feasibility-has-a-uniform-gap: That asks for a finite matrix obstruction; this asks for a tracial representation of the same group with a proved nonembeddable GNS algebra.
artifacts:
  - research/artifacts/leavitt-full-character-classification-2026-09-08.md
---

**OPEN.** Construct a character `chi` of `H=L_(F_2)(1,2)^x` whose
tracial GNS von Neumann algebra is not Connes embeddable.

The classification `binary-leavitt-full-character-simplex` discharges
the previous independent full-group rigidity obligation: such a
character, if constructed, would prove `H` nonhyperlinear. Conversely,
if `H` is nonhyperlinear its canonical regular character is a witness.
This equivalence supplies no witness by itself.

A bad character on an unrelated group, or on a free subgroup of `H`,
does not supply this input. In fact the new subgroup-extension
criterion proves that no bad character of any hyperlinear subgroup
extends to `H`. A construction must directly respect the full group
relations and provide nonembeddability evidence for its resulting trace.
