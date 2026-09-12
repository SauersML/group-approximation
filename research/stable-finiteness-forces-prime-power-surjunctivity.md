---
rg: 2
id: stable-finiteness-forces-prime-power-surjunctivity
kind: claim
title: If F_p[G] is stably finite, every injective cellular automaton over an alphabet of size p^n is surjective
distinct_from:
  stable-finiteness-forces-binary-surjunctivity: that is the p = 2 instance; this is every prime p, reached through stable formalizability rather than unstabilized binary formalizability.
  stable-finiteness-failure-refutes-surjunctivity: that is the converse direction, from a one-sided inverse matrix to a strict linear automaton.
  non-surjunctive-group-with-stably-finite-group-algebras: that is the counterexample target on hosts where all prime-field group algebras are stably finite; this is the positive statement over p-power alphabets for one prime at a time.
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

**OPEN.** Let `p` be prime and `G` a group with `F_p[G]` stably finite. Then every injective cellular
automaton on `(F_p^n)^G` is surjective, for every `n`.

This is Kaplansky's stable finiteness over one prime field implying Gottschalk over the alphabets whose
size is a power of that prime. By `stable-finiteness-reduces-to-prime-field`, any field of
characteristic `p` would do.

## Attempts

- **Route.** `stable-formalizability-reduces-prime-power-surjunctivity`, through
  `prime-field-left-inverse-pairs-are-stably-formalizable`.
- **Known sub-classes.** Formalizable strict pairs, and so sitewise pairs, linear automata, affine and
  disjoint-footprint decoders, and low-degree designs, are all excluded on such hosts.
- **Alphabets.** Surjunctivity over `p^n` symbols gives surjunctivity over every divisor, but never over
  a size with a prime factor other than `p` (`strict-rule-pairs-pass-to-product-alphabets`). Other sizes
  need an alphabet bridge (`strict-rule-pairs-ascend-to-larger-alphabets`, or descent).
- **Where it stops.** Stable formalizability is open (artifact, Section 5).
