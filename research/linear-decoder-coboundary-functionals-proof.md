---
rg: 2
id: linear-decoder-coboundary-functionals-proof
kind: route
title: Pairing the section with an output functional gives a coboundary equation that an ergodic skew product excludes
target: linear-decoders-with-coboundary-functionals-admit-no-section
requires: []
artifacts:
  - research/artifacts/ornstein-weiss-decoder-sections-2026-09-12.md
---

Direct proof, Section 5 of `research/artifacts/ornstein-weiss-decoder-sections-2026-09-12.md`.

1. **Lemma K1: `<x, q>` is not a measurable `a`-coboundary under its hypothesis.**
   - *Finite order.* Telescoping gives a nonzero uniform functional that would vanish.
   - *Infinite order.* Modulo cylinder coboundaries, `<x, q>` is cohomologous to one coordinate per coset. Partial
     sums conjugate the skew product to a Bernoulli shift, which is ergodic, so `omega^(eps + Q)` would be a
     nonconstant invariant function.
2. **Item 1.** `Q(x) = <tau(x), v>` solves the coboundary equation for `<x, q>`, which Lemma K1 excludes.
3. **Item 2.** Kernel translates of the section image give invariant sets of measure `1/|ker L|`, which
   ergodicity excludes.
