---
rg: 2
id: grigorchuk-group-embeds-in-fp-residually-finite-group
kind: claim
title: The first Grigorchuk group embeds in a finitely presented residually finite group
distinct_from:
  bounded-automaton-groups-embed-in-fp-automaton-groups: that asks for a finitely presented automaton overgroup of every bounded automaton group; this is the weaker necessary condition for the Grigorchuk group, with any residually finite finitely presented host.
  spine-hosts-reduce-to-fp-rf-overgroups-of-the-lamp: that shows this condition (in an automaton-embedded form) is necessary and sufficient for self-similar hosts of spine groups over the Grigorchuk group.
  grigorchuk-ascending-hnn-extension-is-finitely-presented: that is a finitely presented overgroup that is not residually finite.
---

**OPEN.** There is a finitely presented residually finite group `R` with `Γ ≤ R`.

## Constraints

- **No endomorphic conjugator.** `R` contains no element conjugating `Γ` into `St_Γ(1)`, for any action of `Γ` as
  a weakly branch group (`rf-hosts-cannot-realize-branch-substitutions`). So Lysenok's L-presentation cannot be
  realized inside `R`.
- **Not virtually torsion-free.** An infinite finitely generated torsion subgroup meets a torsion-free subgroup of
  finite index trivially, so it is finite. This rules out finite-index torsion-free overgroups such as `Aut(F_n)`,
  mapping class groups, right-angled Artin groups and linear groups over fields of characteristic zero.
- **Not linear.** Finitely generated torsion linear groups are finite (Schur).
- **The target for self-similar Boone–Higman.** The automaton-embedded form, `Γ ≤ K ≤ P` with `K` finitely
  presented and `P` a lift-presented automaton group, would make every separated automaton group over the
  Grigorchuk base Boone–Higman through self-similar hosts. This covers spine-Grigorchuk and the spine-mover group
  `M(Γ)` (`spine-hosts-reduce-to-fp-rf-overgroups-of-the-lamp`).

## Status of the literature (bounded search)

Web searches on 09-18 found no finitely presented residually finite group known to contain the Grigorchuk group,
or any infinite finitely generated torsion group. They also found no statement that the question is open.
bh-lit's survey is the place to settle whether it is a named problem.
