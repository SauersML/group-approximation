---
rg: 2
id: every-decidable-group-embeds-in-fp-self-similar-group
kind: claim
title: Every finitely generated group with solvable word problem embeds in a finitely presented self-similar group
refuted_by:
  - self-similar-hosts-contain-only-residually-finite-groups
distinct_from:
  every-fp-rf-group-embeds-in-fp-self-similar-group: that restricts the inputs to finitely presented residually finite groups and is still open; this is the unrestricted universal statement, which is false.
  boone-higman-conjecture: that asks for a finitely presented simple host of any kind; this asks for a finitely presented self-similar host, which would give the conjecture through Zaremsky's theorem but cannot exist for inputs that are not residually finite.
---

**REFUTED.** The statement: for every finitely generated group `G` with
solvable word problem there are `d >= 2` and a finitely presented self-similar
group `H <= Aut(T_d)` with `G <= H`.

Through `fp-self-similar-groups-embed-in-fp-simple-groups` it would imply
`boone-higman-conjecture`, by the route
`boone-higman-via-universal-fp-self-similar-host`. It is false:
`self-similar-hosts-contain-only-residually-finite-groups` shows that Thompson's
V, which has solvable word problem, embeds in no self-similar group.

## Attempts

1. **As a universal route to Boone--Higman.** Proposed 2026-09-12 by the
   Boone--Higman swarm. It dies at once: every self-similar group is residually
   finite, and the inputs that carry the general conjecture, the infinite simple
   ones (`boone-higman-iff-infinite-simple-inputs`), never are. The correct
   residually finite form is `every-fp-rf-group-embeds-in-fp-self-similar-group`.
