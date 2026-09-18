---
rg: 2
id: single-active-symbol-strict-donor-automata-give-every-size
kind: claim
title: A strict donor-covering automaton with one active symbol puts every alphabet size n >= 2 in NS(G)
distinct_from:
  donor-covering-types-give-nonsurjunctive-size-progressions: that gives only the sizes n > z from a type (z, 1); this adds every size 2 <= n <= z, in particular the binary witness 2 ∈ NS(G), by feeding the tag lift into the collapse-lift theorem.
  nonsurjunctive-alphabet-sizes-are-upward-closed: that asks for every larger size from any k ∈ NS(G); this gives every size from one specific kind of strict automaton, via the collapse-lift dichotomy of collapse-lifts-with-unique-largest-fiber-are-surjective (origin commit 708058c4), where the phase lift forces the non-surjective side.
  strict-automata-reach-power-residue-donor-types: that asks for any power-residue type on some group; this shows the one-particle variant listed there already gives a binary witness on the same group.
---

**ESTABLISHED** by `single-active-tag-lift-collapse-proof`. Notation as in
`donor-covering-types-give-nonsurjunctive-size-progressions`.

**Theorem.** If a group `G` carries a strict donor-covering automaton of type `(z, 1)` for some `z >= 1`, then
`NS(G)` contains every integer `n >= 2`. In particular `G` is not surjunctive over two symbols.

**Consequences.**
- The one-particle variant of `strict-automata-reach-power-residue-donor-types` is equivalent to a binary witness
  that also fills every size.
- By `every-group-is-binary-surjunctive`, if binary surjunctivity holds, then every injective donor-covering automaton
  with one active symbol is surjective. This sharpens item 5 of the progression claim from binary-power alphabets to
  the two-symbol case.
- A counterexample to binary surjunctivity may therefore be sought as a strict automaton on any number of symbols
  with one relayed particle.
