---
rg: 2
id: metric-ultraproduct-surjunctivity-from-bounded-width-closures
kind: route
title: A bounded-width closure certificate makes a reverse word infinitesimal in every metric ultraproduct model
target: metric-ultraproducts-of-finite-groups-are-surjunctive
requires:
  - strict-reverse-words-lie-in-bounded-width-profinite-closures
  - surjunctivity-is-axiomatized-by-rectangle-clauses
artifacts:
  - research/artifacts/metric-ultraproduct-bounded-width-closure-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

Artifact, Theorem 1.1, (b) ⇒ (c) ⇒ (a).

- **Transfer to finite groups.** A reverse word `w` in the closure of `Cons_n^F(R_f)` lies in
  `Cons_n^H(R_f(lambda))` at every labelling `lambda` in every finite `H`, because closure membership is membership
  in every finite image.
- **Lift.** Let a metric ultraproduct `Q` realize a strict `D`. Lift the labelling to the factors `H_i`. Forward
  relators have lengths `eps_i -> 0` along `omega`, and every reverse word has limit length at least some `c > 0`.
- **Contradiction.** In each factor some reverse word has length at most `n eps_i`. One word does so for
  `omega`-almost every `i`, which forces its limit length to `0`.

By `surjunctivity-is-axiomatized-by-rectangle-clauses`, `Q` is surjunctive.

This route and `bounded-width-closures-from-metric-ultraproduct-surjunctivity` form an intended equivalence cycle.

**Verification.** `w3-vf-positive` passed this route (Section 10.2 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`).
