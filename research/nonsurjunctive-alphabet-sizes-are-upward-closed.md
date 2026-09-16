---
rg: 2
id: nonsurjunctive-alphabet-sizes-are-upward-closed
kind: claim
title: A group that is not surjunctive over k symbols is not surjunctive over any larger alphabet
distinct_from:
  strict-rule-pairs-ascend-to-larger-alphabets: that is ascent with the tables fixed, for arbitrary table pairs, and it is refuted; this is ascent for one group, where the memories and the realized tables may change.
  ec-groups-share-the-nonsurjunctive-alphabet-sizes: that proves NS(G) closed under multiples and equal to NS_all on existentially closed groups; this asks for closure under every larger size.
  surjunctivity-failure-descends-to-binary-alphabet: that moves the failing size down to two; this moves it up to every larger size.
  table-pair-strict-exactly-at-composite-alphabet-sizes: that is one table pair, realized in no group, whose admissible sizes are the composites; this is ascent for realized data, which that example cannot decide.
artifacts:
  - research/artifacts/composite-size-strict-table-2026-09-16.md
---

**OPEN.** In the notation of `ec-groups-share-the-nonsurjunctive-alphabet-sizes`: for every group `G`, if `k ∈ NS(G)` and
`n >= k`, then `n ∈ NS(G)`. The memories and the realized tables may change.

**Place in the graph.**
- It is the group-level consequence formerly recorded under `strict-rule-pairs-ascend-to-larger-alphabets`. That
  table-level claim is refuted by `table-pair-strict-exactly-at-composite-alphabet-sizes`.
- With `every-group-is-surjunctive-over-binary-power-alphabets` it gives the conjecture
  (`gottschalk-via-upward-closed-nonsurjunctive-sizes`).
- The invalidated route `linear-sofic-surjunctivity-via-formalizability-and-ascent` used only this group-level statement
  for the group at hand, so it can be rebuilt over this claim.
- It holds vacuously if the conjecture holds.

## Attempts

- **Fixed tables** (swarm, 2026-09-16). This was the refuted claim `strict-rule-pairs-ascend-to-larger-alphabets`. A
  2 x 3 table pair is strict exactly at the composite sizes (`table-pair-strict-exactly-at-composite-alphabet-sizes`).
  - What the example is not. It is not realized in any group, since `x_b = 1` forces `(1,a) ~ (b,a)` in the reverse
    table, and the two-digit code needs that coincidence to fail.
  - What it forces. A proof must use that the tables come from a group, or must change the tables, for instance by
    enlarging the memories.
  - Realized pairs cannot help. A table pair realized in a group with any strict size already refutes the
    conjecture, so realized-table ascent cannot be refuted by any example short of that.
  - Artifact `research/artifacts/composite-size-strict-table-2026-09-16.md`, Section 4.
- **Multiples only.** `ec-groups-share-the-nonsurjunctive-alphabet-sizes` gives `k l ∈ NS(G)` for every `l >= 1`, and no
  more. The smallest instance not covered is `k ∈ NS(G)` implies `k + 1 ∈ NS(G)`, for example `2` implies `3`.
- **Passive extensions are dead at group level.** `passive-fixing-injective-automata-are-surjective`: an injective
  automaton that fixes the added symbols in place and writes no added symbol at an original site is surjective. So the
  walls design recorded under `strict-rule-pairs-ascend-to-larger-alphabets` cannot be repaired. An ascent from `A` to
  `A ⊔ D` must write at `D`-sites, or write `D`-symbols at `A`-sites.
- **Existentially closed groups.** `NS(K) = NS_all` for existentially closed `K`, so the claim for one such `K` says
  exactly that `NS_all` is upward closed. That universal form already suffices for the route to the conjecture. The
  per-group form is needed for per-group applications such as linear soficity.
