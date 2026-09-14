---
rg: 2
id: surjunctivity-is-axiomatized-by-rectangle-clauses-proof
kind: route
title: Evaluate both composites on their rectangles and read strict data as universal clauses
target: surjunctivity-is-axiomatized-by-rectangle-clauses
requires: []
artifacts:
  - research/artifacts/gottschalk-rectangle-clauses-and-recognition-2026-09-12.md
---

Complete direct proof: Sections 1 and 2 of the artifact.

- *Evaluation (Lemma 1.2).* At any coordinate, `sigma tau` reads the realized forward
  table of `S x M`, and it is the identity iff `Dec` holds there. `tau sigma` reads
  the realized reverse table of `M x S`, and it is the identity iff `Enc` holds there.
- *Left inverses (Lemma 1.3).* An injective automaton is a homeomorphism onto its
  closed image. Its inverse reads a finite window, and extending that rule
  arbitrarily gives an automaton `sigma` with `sigma tau = id`.
- *Two-table certificate (Theorem 1).* `K` is not surjunctive iff some rules satisfy
  `Dec` and fail `Enc` at the tables realized in `K`. A surjective `tau` with
  `sigma tau = id` has `tau sigma = id`.
- *Monotonicity (Lemma 1.1).* Functions constant on coarser classes are constant on
  finer ones. So `Dec` passes to coarser forward tables and `not Enc` to finer
  reverse tables, and realizability of strict data is the failure of `rho_D`
  (Lemma 2.1, Theorem 2).
- *Consequences (a) to (f).* Universal sentences pass to subgroups and ultraproducts.
  Equational premises and conclusions pass through directed colimits.
  `not rho_D` is existential, so it holds in every existentially closed group once it
  holds in any group. Every labelling satisfying the premises factors through `P(D)`.
