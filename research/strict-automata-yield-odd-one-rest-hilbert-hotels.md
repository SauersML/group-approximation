---
rg: 2
id: strict-automata-yield-odd-one-rest-hilbert-hotels
kind: claim
title: If some group carries a strict automaton, some group carries a strict automaton with one rest symbol, an odd number of active symbols, and a finite active count that never drops
distinct_from:
  strict-automata-reduce-to-few-rest-self-relaying-ones: that asks for death-free witnesses (no active input site ever becomes rest) with at most two rest symbols and any active count; this asks for one rest symbol and an odd active count, and allows deaths as long as the total finite count never drops.
  strict-automata-reduce-to-two-rest-donor-covering-ones: that asks for a local relay structure with two rest symbols; this asks only for a counting property with one rest symbol, which is necessary for every label lift.
  one-rest-donor-covering-strict-automata-raise-the-count: that proves donor-covering one-rest witnesses raise the count; this asks whether any strict automaton with one rest symbol and a count that never drops exists.
  some-nonsurjunctive-group-gives-a-binary-one: that is universal binary descent; this is the counting prerequisite of the affine-relay route to it.
---

**OPEN.** Prerequisite of `universal-binary-descent-via-affine-relay-hotels`.

**Statement.** If `NS_all ≠ ∅`, then some group `G` carries an injective, non-surjective automaton `τ` on
`({0} ⊔ B)^G` with `|B|` odd, `τ(0^G) = 0^G`, and `|τ(ℓ)| >= |ℓ|` for every configuration `ℓ` with finitely many
active sites. Such an automaton then raises the count somewhere (`one-rest-donor-covering-count-proof`, item 3, uses
only these properties).

**Why it is needed.** By `free-orbit-label-lifts-need-count-raising-label-automata`, every equivariant lift through
free orbits with one fixed symbol, and so every label-lift witness over `G × C_q`, has a label automaton of this kind
(apart from the parity of `|B|`, which the affine route needs for item 3 of
`affine-relay-label-lifts-descend-to-two-symbols`).

**What is known.**
- A strict `β` on `A^G` has a power fixing every constant. Declaring one constant symbol rest gives `τ(0^G) = 0^G`,
  but the count may drop, and no reduction that forces monotonicity is known.
- The only count-raising one-rest injective automaton on record is the copying rule on a tree with a fixed end, off
  groups.
- Over amenable, and more generally sofic, groups no strict automaton exists, so the statement is vacuous there.
- Parity. The fix `τ × id_{0,1}` of `self-relaying-donor-covering-automata-reach-admissible-types` turns type `(1, b)`
  into `(1, 2b + 1)`, but it keeps the count monotone only for death-free `τ`. A configuration whose bit layer covers
  `act(τ(ℓ))` but not `act(ℓ)` can lower the count.

## Attempts

- **Quiescent power of the witness** (swarm-0917-w5-gs-binary-descent, 2026-09-17). Take `β^k` fixing all constants,
  one constant symbol rest. `τ(0^G) = 0^G` holds and a weak relay holds: every active input site has an active output
  within the inverse window. Dies at multiplicity. Several active inputs may share the same few active outputs, and
  nothing in injectivity bounds the finite count from below.
- **Parity by a bit layer** (same, 2026-09-17). `τ × id_{0,1}` makes the type odd, but it loses monotonicity whenever
  `τ` has deaths. Dies at configurations whose bit layer covers `act(τ(ℓ))` but not `act(ℓ)`.
