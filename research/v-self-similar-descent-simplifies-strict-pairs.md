---
rg: 2
id: v-self-similar-descent-simplifies-strict-pairs
kind: claim
title: Rewriting a strict pair over V through cylinder copies of V produces a simpler strict pair
refuted_by:
  - v-self-similar-rewrites-preserve-strict-pairs
---

**REFUTED.** This is the hoped-for step of a descent proof of `thompson-v-surjunctive`. Take a
strict pair over `V`. Conjugate its memory into a proper cylinder copy `V_U ~= V`, or split it
along disjoint clopens. The hope was that this yields a strict pair smaller in some invariant of
the pair (its tables, canonical table groups, alphabet or reverse hinges), so that no minimal
strict pair could exist.

## Attempts

- Refuted by `v-self-similar-rewrites-preserve-strict-pairs`. Conjugation keeps the rules and
  both tables, and a product is strict only through a factor whose own tables are unchanged.
  Nothing decreases.
