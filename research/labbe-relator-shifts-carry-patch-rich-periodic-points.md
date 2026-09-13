---
rg: 2
id: labbe-relator-shifts-carry-patch-rich-periodic-points
kind: claim
title: Relator shifts of Labbé's derived full group carry periodic points containing every short legal pattern
refuted_by: [labbe-relator-shift-periodic-points-carry-trivial-actions]
distinct_from:
  labbe-shift-derived-full-group-is-lef: That is the LEF question itself, which non-spatial finite models could also settle; this is the spatial sufficient condition of the relator-shift criterion.
  minimal-free-sft-full-group-pattern-models-are-exact: That concerns infinite validly coloured models; this asks for finite periodic models, which must contain forbidden patterns.
artifacts:
  - research/artifacts/labbe-lef-2026-09-12.md
  - research/artifacts/labbe-lef-crux-small-growth-models-2026-09-13.md
---

**REFUTED (2026-09-13, ex2-labbe-lef-crux, unreviewed).** By
`labbe-relator-shift-periodic-points-carry-trivial-actions`, there is `n_0(S, R)` such that, for `n >= n_0`,
every periodic point of every relator shift carries the trivial action. So (H1) and (H2) fail for every
extension of every radius.

Let `Gamma = D([[Z^2 ~ Omega_U]])` for Labbé's shift, with a finite symmetric generating set `S` and cocycle
radius `R`. Notation is that of `zd-subshift-full-group-lef-via-periodic-relator-shifts`.

**Claim, as originally stated.** For every `n`, there are an extension of radius `R'_n` and a periodic
`y_n ∈ Z_n` with the following two properties.
- (H1) Every pattern of radius `2nR'_n` occurring in `Omega_U` occurs in `y_n`.
- (H2) The period lattice of `y_n` has no nonzero vector of norm `<= 2nR`.

Every such `y_n` shows a forbidden pattern of `Omega_U`. A periodic configuration all of whose windows are legal
would be a periodic point of `Omega_U` (artifact, Section 2, Lemma L2).

## Attempts

- **The refutation (2026-09-13).**
  - The orbit of `y_n` is a finite `n`-exact `F(S)`-set with Schreier growth `<= 9R^2 k^2`.
  - Limits of such models are `Gamma`-sets of quadratic growth. By Matte Bon's classification of confined
    subgroups, each of their orbits is a fixed point or a standard orbit
    (`labbe-full-group-small-growth-actions-are-standard`).
  - So every ball of the model is trivial or orbital, and the orbital charts would build a periodic Wang tiling
    (`labbe-full-group-finite-small-growth-models-are-trivial`).
- **One extension for all `n`.**
  - Mechanism: fix `ĉ_s` once and look for periodic points of `Z_n`.
  - Failure point: if `∩ Z_n = Omega_U`, then `Z_n = Omega_U` for large `n`, and `Omega_U` has no periodic
    points.
    - Otherwise `Gamma` acts on `Z_∞ = ∩ Z_n` and fixes every finite orbit. So periodic points of `Z_∞` contain
      no legal patch on which a generator moves by a non-period.
    - Hence `y_n` must leave some `Z_m` with `m > n` (artifact, Section 3).
- **Gated 3-cycles (heuristic).** Conjugation relators fail at gate boundaries (artifact, Section 6).
- **Gated extensions of ChJN's generators: dead, proved (ex-fp-simple-relation-climbing, 2026-09-13).**
  - Statement: `aperiodic-sft-gated-models-break-refinement-relations`. A refinement relator of bounded length
    fails at the gate boundary.
  - The refutation above supersedes it, covering every extension.
- **Rational perturbation of the polygon exchange.**
  - Mechanism: code a rational rotation by `P_U`.
  - Failure point: sliver atoms code forbidden adjacencies, and nothing controls the relators over them
    (artifact, Section 4).
- **Zero flux (a constraint).** `W(w) = Σ_{z ∈ O} ĉ_w(z)` is a homomorphism `F(S) -> Z^2`, and the defects must
  balance it.
