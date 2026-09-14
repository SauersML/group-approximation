---
rg: 2
id: forward-relations-of-a-counterexample-have-a-nonsofic-core-proof
kind: route
title: Tietze-eliminate private generators of the forward relators and apply Gromov--Weiss to the core
target: forward-relations-of-a-counterexample-have-a-nonsofic-core
requires:
  - surjunctivity-is-axiomatized-by-rectangle-clauses
  - sofic-groups-are-surjunctive
artifacts:
  - research/artifacts/gottschalk-rectangle-clauses-and-recognition-2026-09-12.md
---

Section 6 of the artifact.

- **Peeling.** A generator occurring once in one relator and in no other remaining
  relator is expressed by that relator, and a Tietze move deletes both. Peeling
  reaches the unique 2-core and leaves `P(D) ≅ C(D) * F`.
- **Nonsoficity of the core.** A realized strict `D` makes `P(D)` nonsurjunctive
  (the axiomatization's canonical host), hence nonsofic (Gromov--Weiss). Free
  products of sofic groups with free groups are sofic (Elek--Szabó 2006, not
  re-read in this lane), so `C(D)` is nonsofic. An empty core would make `P(D)`
  free.
- **Filter.** If `C(D) * F` is sofic, its canonical labelling satisfies the decoder
  identity and, being surjunctive, the reverse identity at its own reverse table.
  A realization anywhere would violate that identity at a finer reverse table.
