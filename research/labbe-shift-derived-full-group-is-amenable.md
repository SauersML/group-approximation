---
rg: 2
id: labbe-shift-derived-full-group-is-amenable
kind: claim
title: The derived subgroup of the topological full group of Labbé's minimal aperiodic Wang shift is amenable
distinct_from:
  elek-monod-near-hit-has-torsion-no-kazhdan-subgroup: That records a minimal Z^2 system (Elek--Monod edge colourings) whose alternating group is non-amenable; this asks whether the full group of Labbé's minimal aperiodic Wang shift is amenable.
artifacts:
  - research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md
  - research/artifacts/labbe-full-group-amenability-reductions-2026-09-12.md
---

**OPEN.** Let `Omega_U` be Labbé's 19-tile Wang shift (`minimal-aperiodic-wang-shift-exists`). The group `D([[Z^2 ~ Omega_U]])` is amenable.

## Attempts

- **Juschenko--Nekrashevych--de la Salle (arXiv:1305.2637, Theorem `th:amenhomeo1`, read from source).** Stops.
  - The theorem needs every element to agree locally with an amenable `[[H]]` off a finite set, with recurrent orbital Schreier graphs.
  - The rank-2 interval exchange realizations meet the finite-set clause, since discontinuities of an interval exchange are finitely many points. ChJN line 88 records that those groups are realized as `Z^2` full groups and are amenable.
  - For `Omega_U` the walls are now proved, in Proposition 5 of the reductions artifact. On a singular orbit, two lifts of a point of the torus disagree only along finitely many lattice lines (directions `(1,0)`, `(0,1)`, `(1,-1)`) and strips `n_2 - φ^{-1} n_1 ∈ J`. These sets are not finite.
  - Taking `H = Z^2` makes clause (1) the question itself.
  - This explains why the theorem does not apply. It is not a proof of non-amenability.
- **Orbital recurrence (reductions artifact, Proposition 1, Corollary 2 and Remark 3).** Proved, and not sufficient.
  - Every f.g. subgroup of `[[Z^2 ~ X]]`, for any free action, has recurrent orbital Schreier graphs, by Rayleigh monotonicity and Nash-Williams on `Z^2`. So its orbit actions are extensively amenable (JMMdlS arXiv:1503.04977, `T: recurrent`, `lemma=JSbis`).
  - By JMMdlS `prop:functor:amenable:intro`, amenability follows from any cocycle into a functor `F: I -> Amen` with amenable kernel.
  - Elek--Monod Theorem `main` shows recurrence alone decides nothing: their free minimal Cantor `Z^2`-subshift has `F_2` in its full group, and its orbits are recurrent too.
- **Polygon-exchange model (reductions artifact, Proposition 4, Lemma 6).** Proved from Labbé arXiv:1903.06137, `thm:OmegaU-partition` and `prop:factor-map`.
  - `[[Omega_U]]` embeds in `Sym(T^2 \ Delta)` as polygon exchanges. The translations lie in `φ^{-2} Z^2`, and the cuts have directions `(1,0)`, `(0,1)`, `(1,-1)` and `(1,-φ)`.
  - The JMMdlS rank-2 interval exchange cocycle `τ_g` has wall-shaped support here, so it is not a cocycle into any `F: I -> Amen`. No replacement cocycle is known.
  - A factor map of free Cantor `Z^2`-systems embeds the factor's full group in the extension's. So `F_2` in the full group of any free Cantor factor of `Omega_U` would refute this claim. None is known.
- **Elek--Monod free products (arXiv:1201.0257, lines 66–97).** Not checked.
  - Their faithful `Z/2 * Z/2 * Z/2` uses a homogeneous minimal *proper* edge-colouring that realizes every reduced word as a path.
  - Wang colourings are not proper, so those involutions are undefined as they stand.
  - Whether `[[Omega_U]]` contains `F_2` was not checked.
- **Invariant measure.** Consistent with amenability, but proves nothing. `Omega_U` has a full-support invariant measure (`labbe-shift-derived-full-group-escapes-known-obstructions` item 2), so the compressibility obstruction does not apply.
- **Analogue.** The Penrose tiling group has the same profile: aperiodic, of finite type by matching rules, and minimal. Its amenability is stated open in ChJN, arXiv:1602.04255, line 95.
