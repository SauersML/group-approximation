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
- **Moving one extra bit** (a-gs-upward-closed, 2026-09-17). The design: split one letter `a0` of a strict `τ` into
  `|Q|` letters, and carry the extra data along a local matching of `a0`-sites, or by any injective map that copies
  it by a translation away from the defects. It dies over every group, by
  `translating-transport-split-lifts-are-surjective`.
  - The step where it dies. The lift forces `τ(a0^G) = a0^G`. The cofinite translation makes the finite injection
    `Q^{F \ E} -> Q^{Fs \ E'}` count `|E(τ u)| <= |E(u)|`. Charge noncreation then makes `τ` and the lift surjective.
  - What survives among lifts.
    - One-letter splits whose rest bit map `T_0` on `Q^G` is a bijective automaton that is not a relabelled
      translation. If `T_0` is not surjective, then `|Q| ∈ NS(G)` already.
    - Splits of two or more letters. The charge is then degenerate, and the product lifts giving the multiples sit
      here.
    - Ascents that commute with no letter collapse.
  - By-product. `reversible-automata-that-never-lower-rest-counts-preserve-them` holds over every group, by
    `rest-count-preservation-from-charge-noncreation`. So the count-raising hypothesis of
    `count-raising-reversible-automata-lower-biased-rokhlin-entropy` is never met, and the autonomous star designs die
    unconditionally.
- **Any letter-collapse lift, any rest map** (swarm-0917-w4-gs-upward, 2026-09-17). The first survivor above is
  dead too, and so is the whole collapse class for `k -> k+1`, unless `2 ∈ NS(G)`. By
  `collapse-lifts-with-unique-largest-fiber-are-surjective`, if `Φ` is injective on `B^G`, `r ∘ Φ = τ ∘ r` for a
  letter collapse `r : B -> A` and an injective `τ`, and the largest fiber `Q0` is unique, then either
  `|Q0| ∈ NS(G)` or `τ` and `Φ` are both surjective.
  - The step where the class dies. The rest map `T_0 = Φ|_{Q0^G}` is an injective automaton. If it is not
    surjective, `|Q0|` already fails. If it is bijective, it preserves the uniform Bernoulli measure
    (`bijective-ca-preserve-uniform-bernoulli-measure`). A window count over a finite defect then gives
    `W(τ u) <= W(u)` for the charge `w(a) = log(|Q0| / |Q_a|)`, and charge noncreation makes `τ` and `Φ` surjective.
    The translation of the earlier attempt is no longer needed.
  - Invariant. The fiber charge `W(u) = Σ_g log(|Q0| / |Q_{u(g)}|)`: every collapse lift with a bijective rest map
    conserves it.
  - For `n = k + 1`. Every collapse `B -> A` has a unique fiber of size `2`. So over a group with `2 ∉ NS(G)`, an
    ascent `k -> k+1` must not commute with any letter collapse onto an injective automaton. If `2 ∈ NS(G)`, the
    step `k -> k+1` is needed only for even `k`, because odd `k` gives even `k+1` as a multiple of `2`.
  - What survives. (i) Collapses with at least two largest fibers, for example `(2,2,1)` from `3` to `5`, and the
    product lifts. (ii) Ascents with no collapse onto an injective automaton, for instance lifts over a
    non-injective `τ'`, or block-code factors instead of letter maps.
  - By-product (descent). A strict automaton on `n >= 3` symbols with one autonomously evolving letter, whose
    occurrence set moves by an injective binary automaton, gives `n - 1 ∈ NS(G)`.
- **Dual background, smallest fiber** (swarm-0917-w5-gs-upward, 2026-09-17). This kills survivor (i) above whenever the
  smallest fiber is unique, including the named example `(2,2,1)` from `3` to `5`. By
  `smallest-fiber-collapse-lifts-are-surjective` (established, route `smallest-fiber-collapse-dual-background-proof`),
  suppose `r ∘ Φ = τ ∘ r` with `τ` bijective, `Φ` injective, and a unique smallest fiber `Q0` of size `s`. Then
  `s ∈ NS(G)` (only possible if `s >= 2`), or `Φ` is surjective.
  - The step where the class dies. Replace `Φ` by a power fixing every constant. The rest map on `Q0^G` is then
    bijective, or `s` already fails. The same window count as before gives `W'(u) <= W'(τ u)` with
    `w'(a) = log(|Q_a| / s)`. That is the opposite sign, so it controls `τ^{-1}`, not `τ`. `τ^{-1}` is an automaton that
    fixes `a0^G`, preserves finiteness and never creates `W'`. Charge noncreation gives equality, and the fiber
    injections become bijections.
  - Invariant. The fiber charge relative to the smallest fiber, `W'(u) = Σ_g log(|Q_{u(g)}| / s)`.
  - Consequence for ascent. Suppose a strict collapse design sits over a bijective base, and neither extreme fiber size
    already lies in `NS(G)`. Then it needs two letters of the largest size and two of the smallest (or equal
    fibers). The first undecided profile is `(2,2,1,1)`.
  - Autonomous region. Let `j < n/2` letters have an occurrence set that moves by an injective automaton. Then a strict
    automaton on `n` letters gives `n - j ∈ NS(G)`, and `2 ∈ NS(G)` or `j ∈ NS(G)`. So over a group with
    `2 ∉ NS(G)`, ascent `k -> k + j` by an autonomously moving region of `j < k` new letters needs `j ∈ NS(G)`.
    The case `j = 1` recovers the dead star designs.
  - What survives.
    - Profiles with two letters of each extreme size.
    - A base `τ` that is strict but on fewer letters (`|A| ∈ NS(G)`, which says nothing about `n`).
    - Block-code factors.
    - Coupled dynamics with no factor onto an injective automaton.
