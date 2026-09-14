---
rg: 2
id: some-nonsurjunctive-group-gives-a-binary-one
kind: claim
title: If some group is not surjunctive over some finite alphabet, then some group is not surjunctive over two symbols
distinct_from:
  surjunctivity-failure-descends-to-binary-alphabet: that asks for a binary strict automaton over the same group; this allows any group, so that claim implies this one.
  every-group-is-binary-surjunctive: that is binary surjunctivity of every group; this is the bridge that turns it into the full conjecture.
artifacts:
  - research/artifacts/gk3-alphabet-descent-2026-09-14.md
---

**OPEN.** In the notation of `ec-groups-share-the-nonsurjunctive-alphabet-sizes`: if `NS_all` is nonempty,
then `2 ∈ NS_all`.

**Place in the graph.**
- It is implied by `surjunctivity-failure-descends-to-binary-alphabet`
  (`universal-binary-descent-from-groupwise-descent`), and vacuously by the conjecture itself.
- With `every-group-is-binary-surjunctive` it gives the conjecture (`gottschalk-via-universal-binary-descent`).
- It is equivalent to binary descent for one existentially closed group, and for every existentially closed
  group (`ec-groups-share-the-nonsurjunctive-alphabet-sizes`).

## Attempts

- **Reserved-symbol extensions are dead** (`passive-fixing-injective-automata-are-surjective`, 2026-09-14).
  An injective automaton that leaves a reserved set of symbols in place and writes no reserved symbol at an
  unreserved site is surjective, over every group. A binary coding of a strict automaton must write on
  reserved sites, or write reserved symbols at unreserved ones.
- **Products with a finite group** (artifact Section 4, 2026-09-14).
  - Binary automata over `G × F` are automata on `({0,1}^F)^G` commuting with fiber translation, and local
    phase normalization is always available.
  - The natural design uses default symbols for invalid cells, carries the phase on relay `1`, and tags
    invalid demanded cells. It runs out of free orbits: `k (N - k + 3) > N`.
  - By the barrier, any binary strict automaton over `G × F` must rewrite a constant fiber, or make a
    non-constant fiber constant.
- **Not tried:** phase-borrowing between relays, overgroups of finite index with outer action, and group
  change beyond finite index (artifact Section 5).
