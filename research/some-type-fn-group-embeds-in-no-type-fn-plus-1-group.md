---
rg: 2
id: some-type-fn-group-embeds-in-no-type-fn-plus-1-group
kind: claim
title: "Some group of type F_n (n >= 2) embeds in no group of type F_{n+1}, equivalently in no group of type F_infinity"
---

The negative answer to Zaremsky Problem 1.1: there exists an `n >= 2` and a
group `G` of type `F_n` such that no group of type `F_{n+1}` contains an
isomorphic copy of `G`; a fortiori `G` embeds in no group of type
`F_infinity` (since `F_infinity => F_{n+1}`).

This claim is one of the two admissible answers to the root question
`zaremsky-1-01-type-fn-groups-embed-in-type-fn-plus-1` (once that root is on
main, the route `zaremsky-1-01-by-no` requires this claim). The opposite
answer is "every group of type `F_n` embeds in a group of type `F_{n+1}`
(resp. `F_infinity`)", owned by lane z1-01-embed-pos.

**Precise reading.** For `n >= 2`, type `F_n` implies type `F_2`, i.e. finite
presentability, so both the candidate group `G` and every candidate overgroup
are finitely presented. The question is therefore about *raising* the
finiteness type by an embedding, not about embedding into a finitely
presented group at all (`G` already embeds in itself). Two versions:

- **`F_{n+1}` version:** is there `G` of type `F_n` embedding in no group of
  type `F_{n+1}`?
- **`F_infinity` version:** is there `G` of type `F_n` (or, per Zaremsky, of
  type `F_n` for the strongest reading, any finitely presented `G` when
  `n = 2`) embedding in no group of type `F_infinity`?

A positive answer to either "no group of type F_{n+1}" statement establishes
this claim.

## Attempts

- **The standard reservoir contains no counterexample** (established:
  `standard-fn-not-fn-plus-1-groups-embed-in-type-f-groups`). Every classical
  group of type `F_n` but not `F_{n+1}` -- Bieri--Stallings groups,
  Bestvina--Brady groups `BB_L`, Abels' groups -- is *by construction* a
  subgroup of a group of type `F` (a product of free groups, a right-angled
  Artin group, an S-arithmetic linear group respectively). So all of these
  embed in groups of type `F_infinity`, and a counterexample to Problem 1.1
  would have to be a group of type `F_n` that is not realised as a subgroup of
  any known type-`F` group. This is exactly why no counterexample is known.

- **Cardinality is dead** (established:
  `cardinality-does-not-obstruct-type-f-infinity-embedding`). For `n >= 2` the
  isomorphism types of groups of type `F_n` form a *countable* class (type
  `F_2` = finitely presented, and there are only countably many finite
  presentations), and likewise for type `F_{n+1}` / `F_infinity`. So no
  counting or diagonal-over-uncountably-many argument -- of the kind that
  separates type `FP` from finite presentability (Leary, `2^{aleph_0}` groups
  of type `FP`) -- can force a group of type `F_n` into no group of type
  `F_{n+1}`.

- **Word-problem complexity is dead** (established:
  `unsolvable-word-problem-does-not-obstruct-type-f-infinity`). Type
  `F_infinity` does not bound word-problem complexity: there is a group of
  type `F` with unsolvable word problem (Collins--Miller; Zaremsky Problem
  1.2, answered negatively). So one cannot obstruct the embedding by making
  the word problem of `G` too complicated.

- **The natural universal construction is blocked at level 3** (established:
  `higman-rope-trick-group-is-never-fp3`). Higman's rope trick is the standard
  device for embedding an arbitrary group into an overgroup with better
  finiteness. Fournier-Facio--Zaremsky (arXiv:2607.21727, 2026-07-23, Theorem
  B) show the rope-trick group `Hig_i(G)` of an infinite `G = F/R` (`R != 1`)
  has infinite-dimensional `H_3(-;Q)`, so it is never `FP_3`, hence never
  `F_3` or `F_infinity`. So the obvious positive construction stops at `FP_2`
  and cannot settle Problem 1.1. Their Theorem A instead reduces the positive
  `F`-version to a recursively-presented `FP_n` embedding statement (a
  positive-side lever, for lane z1-01-embed-pos); their Questions 1.3/1.4
  restate the `F_3`/`F_infinity` and `FP_3`/`FP_infinity` embedding questions.
  This is an obstruction to *a method*, not to *all* overgroups, so the
  problem remains open.

- **What a real obstruction would need.** An invariant `I` of a group that (i)
  can be made arbitrarily "large" inside the countable class of type-`F_n`
  groups and (ii) is bounded, for a subgroup, by the type-`F_{n+1}` structure
  of any overgroup. Homological/cohomological dimension is not such an
  invariant (overgroups can have larger dimension), and neither `L^2`-Betti
  numbers nor Novikov--Shubin invariants are known to be monotone under
  passage to type-`F_{n+1}` overgroups. No candidate `I` is known; this is the
  crux and is genuinely open as of the list's date (July 12, 2026).
