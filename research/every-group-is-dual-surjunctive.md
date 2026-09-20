---
rg: 2
id: every-group-is-dual-surjunctive
kind: claim
title: Every post-surjective cellular automaton over every group is pre-injective
distinct_from:
  gottschalk-surjunctivity-conjecture: that says injective automata are surjective; this is Capobianco–Kari–Taati's dual statement that post-surjective automata are pre-injective, hence reversible. No implication between the two universal statements is recorded here.
artifacts:
  - research/artifacts/gk3-dual-surjunctivity-2026-09-14.md
---

**OPEN.** The dual version of Gottschalk's conjecture introduced by
Capobianco, Kari and Taati: for every group `G` and finite alphabet `A`,
every post-surjective automaton `A^G -> A^G` is pre-injective, hence
reversible.

**Known (pinned in `capobianco-kari-taati-dual-surjunctivity-toolkit`).**
- **Sofic groups:** it holds for all of them.
- **Doucha–Gismatullin:**
  - dual surjunctive groups are closed under subgroups and ultraproducts, and form a closed set in the space of marked groups;
  - they satisfy Kaplansky's direct finiteness conjecture over fields of positive characteristic.

**Bridge to Gottschalk.** `post-surjective-decoders-convert-strict-pairs-to-dual-failures`
converts strict pairs with post-surjective decoders into failures of this
claim. The route `gottschalk-via-dual-surjunctivity-and-decoder-transfer`
derives the Gottschalk goal from this claim plus
`dual-surjunctive-groups-are-surjunctive`.

## Attempts

- 2026-09-20 (swarm-0917-w20-w20-gs-last1; group-rings) [class kill]: the homomorphic and affine sector is closed.
  The claim stays OPEN.
  - *Landed.* `homomorphic-post-surjective-automata-are-automorphisms` (ESTABLISHED; artifact
    `research/artifacts/homomorphic-post-surjective-automata-2026-09-19.md`).
    - Every post-surjective homomorphic automaton over a finite group alphabet `V` is an automorphism once
      `M_n(F_p[G])` is directly finite at the abelian composition primes of `V` with `p^n <= |V|`.
    - This is unconditional at every group when `V` has no abelian composition factor.
    - This sector of the claim holds at `G` iff every `F_p[G]` is stably finite, the same condition as the
      homomorphic sector of Gottschalk.
  - *Where it dies for general automata.* The invariant is a group structure on `A` making the automaton a heap
    morphism. The proof uses it twice:
    - to turn post-surjectivity into onto-ness of a *subgroup* `V[G]`, which is then pushed through the derived
      series;
    - to count factor sites in the centerless layer.
  - A nonaffine automaton has no invariant filtration of its alphabet, so neither step is available.
  - Counterexamples at groups whose `F_p[G]` are stably finite must be nonaffine for every group structure on `A`.
