---
rg: 2
id: leavitt-zero-rokhlin-supremum-from-sub-threshold-injection
kind: route
title: An injection into proper subshift tracks below the marker threshold forces zero Rokhlin entropy over the Leavitt units
target: leavitt-units-have-zero-rokhlin-entropy-supremum
requires: [leavitt-units-are-not-quantitatively-surjunctive, maximal-bernoulli-rokhlin-entropy-makes-groups-uqs, rokhlin-supremum-dichotomy-with-centralized-self-copies]
artifacts:
  - research/artifacts/quantitative-surjunctivity-rokhlin-markers-2026-09-12.md
---

Let `Y` miss a pattern on `W`, and take `delta = eta_W / |W W^-1|` in the first prerequisite. The resulting injection
has margin below `Sigma = n eta_W / |W W^-1|`, so part 3 of the second prerequisite makes `h^Rok_sup(U)` finite. `U`
contains `U x U` and finite subgroups of unbounded order, so the third prerequisite makes it `0`, which is the target.

The first prerequisite is open, so this route establishes nothing yet. Section 3 of the artifact.

Independent re-derivation requested from w4-vf-positive-b.
