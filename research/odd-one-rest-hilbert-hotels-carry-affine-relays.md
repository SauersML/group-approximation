---
rg: 2
id: odd-one-rest-hilbert-hotels-carry-affine-relays
kind: claim
title: If some group carries a strict one-rest automaton of odd type whose finite active count never drops, some group carries one with an integral affine phase relay
distinct_from:
  donor-covering-few-rest-automata-reach-admissible-types: that is a 2-adic type reduction for donor-covering automata; this asks for an algebraic relay certificate on a count-monotone automaton, with no 2-adic step.
  strict-automata-yield-odd-one-rest-hilbert-hotels: that is the counting prerequisite; this is the local algebraic prerequisite that turns counting into a lift.
  affine-relay-label-lifts-descend-to-two-symbols: that proves relays suffice; this asks whether relays can be found once the necessary count condition holds.
---

**OPEN.** Prerequisite of `universal-binary-descent-via-affine-relay-hotels`. Notation as in
`affine-relay-label-lifts-descend-to-two-symbols`.

**Statement.** Suppose some group carries a strict automaton `τ` on `({0} ⊔ B)^G` with `|B|` odd, `τ(0^G) = 0^G`, and a
finite active count that never drops. Then some group `G'` carries a strict automaton of the same kind, with `|B'|`
odd, that has an integral affine relay (R1)-(R3).

**Where the gap is.**
- **Counting versus matching.** (R3) implies Hall's condition on every finite set of active input sites, along
  window-sized neighbourhoods, and hence a global injection from active inputs into active outputs. A count that never
  drops gives this only for finite configurations taken as a whole, not for finite subsets of an infinite
  configuration, since outputs near the edge of the subset see the rest of the configuration.
- **Matching versus relay.** A donor relay is a locally defined matching. An affine relay needs no local matching, but
  it needs injectivity of sparse integral linear maps mod every prime on *all* vectors. On a region with one label
  pattern this is a condition on a single element of `Z[G]` of augmentation `1` (heuristic remark in the relay node).
  Over `Z`, a linear rule on `(Z/p)^Z` is injective only if it is a monomial, so there relays reduce to donors on such
  regions. Over other groups non-monomial injective elements of `F_p[G]` are available, for example units
  `1 + (1 - g) h (1 + g + ... + g^(k-1))` when `g` has order `k`.
- **Freedom.** The statement allows a change of group, memory and alphabet, for example powers of `τ`, products with
  bijective automata, and tag multiplication by `θ_n`.

## Attempts

- **Donors from Hall matchings** (swarm-0917-w5-gs-binary-descent, 2026-09-17). Counting gives Hall's condition only
  for finite configurations. Even where a matching exists, it is not locally computable from symmetric data (compare
  Step 6 of `arrow-shift-strict-automata-proof`). This is why the relay is algebraic here, and it stops before any
  construction of a non-donor relay on a non-surjective automaton.
