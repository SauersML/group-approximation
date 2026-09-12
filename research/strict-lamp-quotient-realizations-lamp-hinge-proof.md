---
rg: 2
id: strict-lamp-quotient-realizations-lamp-hinge-proof
kind: route
title: A forward-sufficient lift to the surjunctive wreath would be bijective, and coarsening would make the quotient realization surjective
target: strict-lamp-quotient-realizations-need-lamp-hinges
requires:
  - kun-thom-nonsofic-wreaths-are-surjunctive
  - strict-automata-live-on-canonical-table-groups
artifacts:
  - research/artifacts/kun-thom-lamp-quotient-hosts-2026-09-12.md
---

The quotient map carries the lift to the realization, so the lift's tables refine the
realization's tables. If the lift's forward table were sufficient, its automaton would be
injective over `W`, hence bijective because `W` is surjunctive. Its reverse table would then be
sufficient, and so would the coarser reverse table of `rho` (Lemmas 2--3 of the canonical
table-group artifact), which makes `tau_rho` surjective. So the lift's forward table is
insufficient. A coincidence present for `rho` and absent for the lift has a hinge word that dies
in `W/U` without being trivial in `W`. Theorem D of the artifact.
