---
rg: 2
id: strict-automata-reduce-to-two-rest-donor-covering-ones
kind: claim
title: If some group carries a strict automaton, some group carries a strict donor-covering automaton with two rest symbols and an active alphabet of size not divisible by four
distinct_from:
  some-nonsurjunctive-group-gives-a-binary-one: that is universal binary descent in terms of alphabet sizes; this is the same statement rewritten by donor-covering-strict-automata-descend-to-two-symbols, where only the number of rest symbols must drop and the active symbols can be multiplied freely.
  surjunctivity-failure-descends-to-binary-alphabet: that asks for descent on the same group; this allows any group and fixes only the rest alphabet.
  one-rest-donor-covering-strict-automata-raise-the-count: that proves what a one-rest witness must do; this asks whether some witness with at most two rest symbols exists.
---

**OPEN.** Notation as in `donor-covering-strict-automata-descend-to-two-symbols`. If `NS_all ≠ ∅`, then some group
carries a strict donor-covering automaton of type `(2, b)` with `4 ∤ b`.

**Equivalent form.** By item 5 of `donor-covering-strict-automata-descend-to-two-symbols`, this claim is equivalent to
`some-nonsurjunctive-group-gives-a-binary-one`. Every strict automaton already gives type `(k, k)` with `k = |A|`,
and item 2 multiplies `b` by any factor. So the claim is exactly **rest-symbol reduction**: from type `(k, k)` to
type `(2, b)` with `4 ∤ b`, over some group.

**Stronger variant.** Type `(1, b)` with `b` odd also suffices (item 4). A witness of that type must raise the active
count on some finite configuration (`one-rest-donor-covering-strict-automata-raise-the-count`).

**Known cases.** If the strict witness is linear over a field of characteristic two, a binary witness over `G × P`
exists (`modular-matrix-failures-descend-to-scalars-over-g-times-p`), and item 5 turns it into type `(2, 2)`. Sofic
groups carry no strict automata at all.

**Structure of a type `(2, b)` witness.** An all-rest neighbourhood has no donor, so its output is a rest symbol.
Hence the witness maps `Z^G` into itself, and its restriction there is an injective binary automaton. Over a
binary-surjunctive group that restriction is a bijection, and strictness must come from configurations with active
sites.

## Attempts

- **Reclassifying rest symbols as active** (a-gs-binary-descent, 2026-09-17). Start from `β × id` of type
  `(k, k)` and declare all but two rest symbols active. It dies at (D2). A site holding a reclassified symbol whose
  `β`-output is one of the two kept rest symbols has no relay, and nothing nearby is obliged to be active. Any fix
  must create active outputs near such sites, and with one rest symbol it must raise the count.
