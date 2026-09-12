---
rg: 2
id: strict-automata-closed-under-host-manipulations
kind: claim
title: Strict automata are closed under host conjugation, endomorphism transport, composition and products
distinct_from:
  rokhlin-supremum-dichotomy-with-centralized-self-copies: that uses self-copies to force a zero-or-infinite Rokhlin supremum; this records that conjugation, transport along injective endomorphisms such as the commuting Leavitt copies, composition and products all preserve strictness, so these host features alone yield no contradiction.
  surjunctivity-passes-to-subgroups: that is heredity of surjunctivity to subgroups; this is closure of the class of strict automata over one host under the operations the host supplies.
artifacts:
  - research/artifacts/simple-host-direct-attack-2026-09-12.md
---

Let `tau` and `rho` be injective automata over `G`, with `tau` strict (injective and not onto).
Each of the following is strict:

- **Conjugation:** `tau^c = R_c tau R_(c^-1)`, the automaton with memory `c M c^-1`, for
  `c in G`.
- **Transport:** the automaton with memory `alpha(M)` and the same rule, for an injective
  endomorphism `alpha` of `G`.
- **Composition:** `tau o rho` and `rho o tau`.
- **Products:** `tau x rho` over a product alphabet.

Also, `tau` is strict iff its restriction to any subgroup containing its memory is strict.

**On `R^x`.** Transport along the commuting copies `g -> s0 g t0 + s1 t1` and
`g -> s0 t0 + s1 g t1`, or along the doubling `g -> s0 g t0 + s1 g t1`, turns one strict automaton
into commuting strict automata. Their composite is strict and misses independent patterns.

**Consequence.** Strict automata form a two-sided ideal of the monoid of injective automata, closed
under everything the host supplies. None of these operations produces a bijection from a strict
automaton, so a contradiction on a simple host has to come from a size that drops on proper
retracts. By `surjunctivity-iff-automaton-monoid-directly-finite`, that is direct finiteness of the
automaton monoid.

Proposition 3 of the artifact.
