---
rg: 2
id: binary-left-inverse-pairs-over-fg-simple-groups-are-formalizable
kind: claim
title: Every binary left-inverse automaton pair over a finitely generated simple group is formalizable
distinct_from:
  binary-left-inverse-pairs-are-formalizable: that asks for formalizability over every group and is refuted over the integers; this asks only over finitely generated simple groups, where no landed refutation applies.
  injective-binary-automata-are-stably-formalizable: that allows ancilla tracks over every group; this asks for plain formalizability, but only over finitely generated simple hosts, which is where the Kaplansky payoff needs it.
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
---

**OPEN.** Let `S` be a finitely generated simple group and `tau`, `sigma` automata on `(F_2^n)^S` with
`sigma o tau = id`. Then some polynomial representatives of their local rules, on finite memories,
satisfy `sigma~ o tau~ = id` as a formal polynomial identity.

**Why it matters.**
- **Per host.** With `formal-polynomial-strict-pairs-need-unstable-linearization`, it makes every finitely
  generated simple `S` with stably finite `F_2[S]` surjunctive over binary-power alphabets
  (`stably-finite-simple-hosts-are-binary-power-surjunctive`).
- **Every group.** Gottschalk reduces to such hosts (`gottschalk-reduces-to-fg-simple-kazhdan-groups`).
  So Kaplansky stable finiteness over `F_2` for all groups would then give Gottschalk over binary-power
  alphabets.

## Attempts

- **The landed refutations do not reach these hosts.**
  - The marker involutions over `Z` and `Q` rest on one-track affine rigidity over bi-orderable groups.
    No nontrivial finitely generated simple group is bi-orderable
    (`finitely-generated-simple-groups-are-not-biorderable`).
  - Finite quotients: a host without proper finite-index subgroups has only the constant level, and over
    `F_2` every permutation there is tame.
  - Pushforward along quotients of the encoder memory group
    (`formal-pairs-push-along-quotients-of-the-encoder-memory-group`) is void once the memory generates
    the simple host.
- **One-track rigidity fails here.** Hosts with 2-torsion carry non-affine one-track formal involutions
  (`non-central-involutions-carry-nonaffine-formal-involutions`).
- **Strict pairs need more than gates.** A formal pair for a strict `tau` has an encoder pullback that is
  surjective but not injective. Words in formal automorphisms, including zero-divisor shears
  (`zero-divisor-shears-are-formal-automorphisms`), never have this property.
- **First test objects.** The marker involution along an infinite-order element, induced to Thompson's
  `V`. Any formalization must use encoder memory in which every bi-orderable quotient kills that element.
