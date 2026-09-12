---
rg: 2
id: bounded-width-closures-from-metric-ultraproduct-surjunctivity
kind: route
title: Capped conjugation word lengths turn a failed bounded-width closure into a strict clause over a metric ultraproduct
target: strict-reverse-words-lie-in-bounded-width-profinite-closures
requires:
  - metric-ultraproducts-of-finite-groups-are-surjunctive
  - surjunctivity-is-axiomatized-by-rectangle-clauses
artifacts:
  - research/artifacts/metric-ultraproduct-bounded-width-closure-2026-09-12.md
---

Artifact, Theorem 1.1, (a) ⇒ (c) ⇒ (b).

- **Product trick.** Suppose no reverse word of a strict `D` lies in the closure of `Cons_n^F(R_f)`. Each reverse
  word then survives outside `Cons_n` in some finite image. The product of these images gives one labelling at which
  every reverse word lies outside `Cons_n` of the forward relators.
- **Capped lengths.** On that finite group take `l_n = min(1, len_n / n)`, with `len_n` the conjugation-invariant word
  length with respect to the forward relators. Relators have length at most `1/n`, and reverse words have length `1`.
- **Ultraproduct.** Along a nonprincipal ultrafilter on `n`, the metric ultraproduct realizes `D`. So it is not
  surjunctive, by `surjunctivity-is-axiomatized-by-rectangle-clauses`.

This route and `metric-ultraproduct-surjunctivity-from-bounded-width-closures` form an intended equivalence cycle.
