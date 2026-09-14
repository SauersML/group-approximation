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
- **Dead route:** `formalizable-pairs-reduce-surjunctivity-to-kaplansky`. Its prerequisite fails
  (`binary-left-inverse-pairs-need-not-be-formalizable`, gk-fz-bennett): over bi-orderable groups a
  formalizable one-track binary pair is a shift plus a constant, so the marker involution on
  `{0,1}^Z` is not formalizable on its own alphabet. The weaker original-alphabet claim
  `injective-binary-automata-have-formalizable-left-inverses` fails for the same automaton, because a
  bijective automaton has a unique left inverse.
- **Live route:** `stable-formalization-reduces-surjunctivity-to-kaplansky`, through
  `injective-binary-automata-are-stably-formalizable` (identity ancilla tracks). With ancillas the
  extreme variable can cancel between components, so the one-track obstruction does not apply.
- **Where it stops.** No ancilla construction is known for any one-track non-affine automaton on a
  bi-orderable group. The first test is the marker involution with one ancilla (artifact,
  Section 6.4).
