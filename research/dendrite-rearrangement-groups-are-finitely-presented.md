---
rg: 2
id: dendrite-rearrangement-groups-are-finitely-presented
kind: claim
title: The rearrangement groups G_n of the Ważewski dendrites D_n are finitely presented
distinct_from:
  dendrite-rearrangement-group-g3-has-simple-commutator-subgroup: that proves the commutator subgroups [G_n, G_n] are simple for all n ≥ 3; this asks whether the groups G_n themselves are finitely presented.
artifacts:
  - research/artifacts/gq-bh-openq-lists.md
---

**OPEN.** M. Tarocchi, *On Thompson groups for Ważewski dendrites*,
arXiv:2310.14660v3, TeX l.1079–1085:

> Now that we know that each $G_n$ is finitely generated, it is natural to ask the
> following question, which we do not investigate here.
> What further finiteness properties do dendrite rearrangement groups have? Are they
> finitely presented? Are they $F_\infty$?

The same question is in Tarocchi's thesis, arXiv:2412.02339, TeX l.5158–5163.

**Why it sits next to Boone–Higman.**
- By `dendrite-rearrangement-group-g3-has-simple-commutator-subgroup` and Tarocchi's
  Theorem `thm:comm:simple`, each `[G_n, G_n]` is an infinite simple group.
- It is finitely generated (Theorem `thm:comm:fg`) and lies in Thompson's `V`.
- `G_n/[G_n, G_n] ≅ Z/2 ⊕ Z` (Theorem `thm:commutator`).
- So finite presentation of `G_n` would pass to the index-2 subgroup `Π^{-1}(0)`, and
  from there to `[G_n, G_n] = Ker Δ|` only through a BNS-type condition on the
  character `Δ`. If both held, these would be finitely presented simple groups built
  from a dendrite rather than from a Cantor set.

**Route.** Rearrangement groups act properly on CAT(0) cube complexes
(Belk–Forrest, recalled in Tarocchi §`sub:rearrangements`). The Stein–Farley
Morse-theory method, as used for the Basilica and airplane rearrangement groups, is
the natural first attempt.
