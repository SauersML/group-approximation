---
rg: 2
id: labbe-shift-derived-full-group-is-amenable
kind: claim
title: The derived subgroup of the topological full group of Labbé's minimal aperiodic Wang shift is amenable
distinct_from:
  elek-monod-near-hit-has-torsion-no-kazhdan-subgroup: That records a minimal Z^2 system (Elek--Monod edge colourings) whose alternating group is non-amenable; this asks whether the full group of Labbé's minimal aperiodic Wang shift is amenable.
artifacts:
  - research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md
---

**OPEN.** Let `Omega_U` be Labbé's 19-tile Wang shift (`minimal-aperiodic-wang-shift-exists`). The group `D([[Z^2 ~ Omega_U]])` is amenable.

## Attempts

- **Juschenko--Nekrashevych--de la Salle (arXiv:1305.2637, Theorem `th:amenhomeo1`, read from source).** Stops.
  - The theorem needs every element to agree locally with an amenable `[[H]]` off a finite set, with recurrent orbital Schreier graphs.
  - The rank-2 interval exchange realizations meet the finite-set clause, since discontinuities of an interval exchange are finitely many points. ChJN line 88 records that those groups are realized as `Z^2` full groups and are amenable.
  - For `Omega_U` no candidate `H` was found. Changes of translation vector occur along cylinder boundaries, which on each orbit `Z^2` form 1-dimensional walls, not finite sets.
  - This is a heuristic reason the theorem does not apply, not a proof of non-amenability.
- **Elek--Monod free products (arXiv:1201.0257, lines 66–97).** Not checked.
  - Their faithful `Z/2 * Z/2 * Z/2` uses a homogeneous minimal *proper* edge-colouring that realizes every reduced word as a path.
  - Wang colourings are not proper, so those involutions are undefined as they stand.
  - Whether `[[Omega_U]]` contains `F_2` was not checked.
- **Invariant measure.** Consistent with amenability, but proves nothing. `Omega_U` has a full-support invariant measure (`labbe-shift-derived-full-group-escapes-known-obstructions` item 2), so the compressibility obstruction does not apply.
- **Analogue.** The Penrose tiling group has the same profile: aperiodic, of finite type by matching rules, and minimal. Its amenability is stated open in ChJN, arXiv:1602.04255, line 95.
