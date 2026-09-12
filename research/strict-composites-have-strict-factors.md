---
rg: 2
id: strict-composites-have-strict-factors
kind: claim
title: A strict composite of automata on one full shift has a strict factor
distinct_from:
  linear-reversible-words-strict-via-strict-linear-factor: that extracts a strict linear factor from words in square linear and bijective automata over F_q; this is the same induction for factors of any kind, with the consequence that composites of surjunctive automata are surjunctive.
artifacts:
  - research/artifacts/radu-lattice-strict-automaton-screens-2026-09-12.md
---

**ESTABLISHED** by `strict-composites-have-strict-factors-proof`.

Let `G` be a group, `A` a finite alphabet, and `tau_1, ..., tau_k` cellular automata on `A^G`. If
`tau = tau_1 ... tau_k` is injective, every tail `tau_j ... tau_k` is injective. If moreover `tau` is not
surjective, some factor `tau_j` is injective and not surjective.

**Consequences.**
- Call an automaton surjunctive when injectivity implies surjectivity. Then composites of surjunctive
  automata are surjunctive.
- If the memory of `tau_j` lies in a surjunctive subgroup `S`, then `tau_j` acts as the same automaton
  over `S` on every factor of `A^G = prod_(gS) A^(gS)`, so it is surjunctive. No composite of
  automata whose memories lie in surjunctive subgroups is strict, even when different factors use
  different subgroups, for example amenable, sofic or free ones.
- On a lattice in a product of trees, alternating horizontal-memory and vertical-memory automata are
  never strict. On Radu's BMW lattice every letter is an involution, so layers reading only the
  corners of one square have dihedral memory and add nothing (`radu-bmw-lattice-nonsurjunctive`,
  Attempts).

The alphabet must stay fixed. Gathering windows into larger alphabets presents every automaton as a
composite.

Proof: Section 2 of the artifact.
