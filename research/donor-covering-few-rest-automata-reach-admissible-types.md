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
- **Zero-rest reading of the hypothesis** (swarm-0917-w19-w19-gs-last1, 2026-09-19). This is a scope obstruction, not
  a proof. By `few-rest-type-reduction-is-per-group-binary-descent`, every strict automaton `β` on `A^G` is
  donor-covering of type `(0, |A|)`, with `Z = ∅`, `B = A` and `d ≡ 1`, and this node lists `(0, b)` as in scope. So,
  as stated, the node is equivalent to `(P)`: every group with `NS(G) ≠ ∅` carries an admissible type.
  - Given items 3 and 4 of `donor-covering-strict-automata-descend-to-two-symbols`, `(P)` implies universal binary
    descent on its own. Restricted to existentially closed groups, `(P)` is equivalent to it.
  - `(P)` also forces `NS(G)` to contain sizes prime to any finite set of odd primes, with `4 ∤ n`.
  - So this node is not the last-mile 2-adic step it was read as. The route `donor-covering-phase-transport-proof`
    reformulates its target and does not reduce it.
  - The genuine 2-adic content is the case `z ∈ {1, 2}`: types `(1, b)` with `b` even and `(2, b)` with `4 | b`,
    whose births relay to donors other than themselves (the self-relaying case is established). Future attempts
    should state which case they attack.
