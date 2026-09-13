---
rg: 2
id: labbe-relator-shifts-carry-patch-rich-periodic-points
kind: claim
title: Relator shifts of Labbé's derived full group carry periodic points containing every short legal pattern
distinct_from:
  labbe-shift-derived-full-group-is-lef: That is the LEF question itself, which non-spatial finite models could also settle; this is the spatial sufficient condition of the relator-shift criterion.
  minimal-free-sft-full-group-pattern-models-are-exact: That concerns infinite validly coloured models; this asks for finite periodic models, which must contain forbidden patterns.
artifacts:
  - research/artifacts/labbe-lef-2026-09-12.md
---

**OPEN.** Let `Gamma = D([[Z^2 ~ Omega_U]])` for Labbé's shift, with a finite symmetric generating set `S` and cocycle radius `R`. Notation is that of `zd-subshift-full-group-lef-via-periodic-relator-shifts`.

Is there, for every `n`, an extension of radius `R'_n` and a periodic `y_n ∈ Z_n` with the following two properties?
- (H1) Every pattern of radius `2nR'_n` occurring in `Omega_U` occurs in `y_n`.
- (H2) The period lattice of `y_n` has no nonzero vector of norm `<= 2nR`.

Every such `y_n` shows a forbidden pattern of `Omega_U`. A periodic configuration all of whose windows are legal would be a periodic point of `Omega_U` (artifact, Section 2, Lemma L2).

## Attempts

- **One extension for all `n`.**
  - Mechanism: fix `ĉ_s` once and look for periodic points of `Z_n`.
  - Failure point: if `∩ Z_n = Omega_U`, then `Z_n = Omega_U` for large `n`, and `Omega_U` has no periodic points.
    - Otherwise `Gamma` acts on `Z_∞ = ∩ Z_n` and fixes every finite orbit. So periodic points of `Z_∞` contain no legal patch on which a generator moves by a non-period.
    - Hence `y_n` must leave some `Z_m` with `m > n` (artifact, Section 3).
- **Gated 3-cycles (heuristic, not proved).**
  - Mechanism: take 3-cycle generators, shrink their pattern sets so that triples never overlap, and move only when every window read is legal.
  - Failure point: commutation relators between disjointly supported elements survive.
    - Conjugation relators `tau_1 tau_2 tau_1^{-1} = tau_3` fail at gate boundaries, where a defect closes one gate and not the other (artifact, Section 6).
- **Rational perturbation of the polygon exchange.**
  - Mechanism: code a rational toral rotation by the partition `P_U` (Labbé arXiv:1903.06137, abstract only). This gives periodic configurations with small defect density.
  - Failure point: some atom codes a forbidden adjacency, and every generic orbit meets such a sliver (artifact, Section 4). Nothing controls the relators over the slivers.
- **Zero flux (a constraint, not an obstruction).**
  - `W(w) = Σ_{z ∈ O} ĉ_w(z)` is a homomorphism `F(S) -> Z^2` on the orbit `O` of `y_n`.
  - It vanishes on the generators once `2n` exceeds the length of relators that write each generator as a product of commutators. The defects must balance the flux exactly.
