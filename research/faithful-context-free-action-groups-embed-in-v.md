---
rg: 2
id: faithful-context-free-action-groups-embed-in-v
kind: claim
title: "A finitely generated group with a faithful context-free action embeds in Thompson's group V"
artifacts:
  - research/artifacts/twisted-power-cloning-cf-action-2026-09-16.md
---

Let `G = ⟨A⟩` be a finitely generated group, `A` a finite symmetric generating
set. Suppose `G` acts faithfully on the right on a set `X` with finitely many
orbits, and for one point `ξ` in each orbit the loop language

`L(ξ) = { w ∈ A^* : ξ·w = ξ }`

of the orbital Schreier graph `Sch(ξ·G, G; A)` is a context-free language.
Then `G` is isomorphic to a subgroup of Thompson's group `V`.

This is the "if" direction of the Bodart–D'Angeli–Perego–Rodaro
characterisation of finitely generated subgroups of `V` (an action with
finitely many orbits whose orbital Schreier graphs are context-free is what
they call a *context-free action*; a group with a faithful one is `CF-TR`).
It is the tool used to embed twisted direct-power Thompson groups in `V`
(`twisted-power-cloning-groups-embed-in-v`). Established by literature import;
see `faithful-context-free-action-groups-embed-in-v-citation`.
