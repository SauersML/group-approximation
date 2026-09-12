---
rg: 2
id: stable-finiteness-forces-binary-surjunctivity
kind: claim
title: If F_2[G] is stably finite, every injective cellular automaton over an alphabet of size 2^n is surjective
distinct_from:
  stable-finiteness-failure-refutes-surjunctivity: that is the converse, where a one-sided matrix inverse over a finite field gives a strict linear automaton; this asks whether stable finiteness over F_2 alone forces surjunctivity over every binary-power alphabet.
  non-surjunctive-group-with-stably-finite-group-algebras: that is a counterexample target on hosts with stably finite prime-field group algebras, over any alphabet; this is a positive statement over binary-power alphabets only, so neither is the negation of the other.
  sofic-groups-are-surjunctive: that derives surjunctivity from soficity; this would derive it from stable finiteness over F_2, a weaker hypothesis on the host, but only over binary-power alphabets.
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
---

**OPEN.** Let `G` be a group with `F_2[G]` stably finite. Then every injective cellular automaton
on `(F_2^n)^G` is surjective, for every `n`.

This is Kaplansky's stable finiteness over `F_2` implying Gottschalk over binary-power alphabets.
The converse direction is `stable-finiteness-failure-refutes-surjunctivity`.

## Attempts

- **Classes already known to satisfy it:**
  - linear automata, and more generally every pair whose left-inverse identity is formal
    (`formal-polynomial-strict-pairs-need-unstable-linearization`);
  - affine decoders, and decoders with disjoint encoder footprints
    (`disjoint-footprint-decoders-force-kaplansky-failure`);
  - sitewise automata.
- **Route:** `formalizable-pairs-reduce-surjunctivity-to-kaplansky`, through
  `binary-left-inverse-pairs-are-formalizable`.
- **Where it stops.** No mechanism turns a functional left-inverse identity that needs `x^2 = x`
  into a formal one (artifact, Section 6.4).
