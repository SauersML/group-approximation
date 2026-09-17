---
rg: 2
id: donor-covering-few-rest-automata-reach-admissible-types
kind: claim
title: A group carrying a strict donor-covering automaton with at most two rest symbols carries one of type (2, b) with 4 ∤ b or (1, b) with b odd
distinct_from:
  donor-covering-strict-automata-descend-to-two-symbols: that is the descent statement for every type with at most two rest symbols; this is only the 2-adic type reduction its proof route is missing.
  strict-automata-reduce-to-two-rest-donor-covering-ones: that starts from an arbitrary strict automaton and allows any group; this starts from at most two rest symbols and keeps the group.
  one-rest-donor-covering-strict-automata-raise-the-count: that proves what a one-rest witness must do; this asks for a change of the active alphabet's 2-adic valuation, or of the number of rest symbols.
---

**OPEN.** Notation as in `donor-covering-strict-automata-descend-to-two-symbols`. Let `G` carry a strict
donor-covering automaton of type `(z, b)` with `z <= 2`. Then `G` carries a strict donor-covering automaton of type
`(2, b')` with `4 ∤ b'`, or of type `(1, b')` with `b'` odd.

**Why it matters.** Items 1-5 of `donor-covering-phase-transport-proof` reach only those admissible types. Tag
multiplication (item 2) multiplies `b` and never lowers its 2-adic valuation, so types such as `(2, 4)`, `(1, 2)` and
`(0, b)` are not covered. The referee audit of 2026-09-17 refuted the descent claim at exactly this step.

## Attempts

- **Tag multiplication** (audit, 2026-09-17). Item 2 of `donor-covering-phase-transport-proof` turns type `(z, b)`
  into `(z, bt)`. It dies at once: the 2-adic valuation of `bt` is at least that of `b`, and `z` is unchanged. Any
  reduction must either merge active symbols or change the number of rest symbols, and (D2) must survive that.
