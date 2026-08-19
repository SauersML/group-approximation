---
rg: 2
id: kun-thom-clifford-relative-wall
kind: claim
title: Finite normalized-HS Clifford wall for the Kun--Thom pair
distinct_from:
  kun-thom-clifford-extension-not-weak-mf: That settles the operator-norm question for the Clifford extension in the negative, so it is a completed no-go in the MF category; this asks for a normalized-Hilbert--Schmidt construction in the tracial category, which that result does not touch and in fact predicts must avoid the operator-norm sector entirely.
artifacts:
  - notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md
  - notes/TRUE_CLIFFORD_HYPERLINEARITY_FORCES_AMBIENT_HS_INSTABILITY.md
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
  - notes/FALSE_RELATIVE_WALL_FORCES_FLEXIBLE_HS_INSTABILITY.md
  - notes/FALSE_ONE_INVOLUTION_INSTABILITY.md
  - GroupApproximation/Sofic/CliffordPhaseExtraction.lean
  - GroupApproximation/Sofic/AntipodalRadicalCollision.lean
---

Construct normalized-Hilbert--Schmidt almost-representations
`rho_n:G->U(d_n)` and self-adjoint involutions `C_n` such that `C_n`
asymptotically commutes with every fixed element of `Gamma`, while

```text
C_(h,n)=rho_n(h) C_n rho_n(h)^*,
||C_n C_(h,n)+C_(h,n) C_n||_2 -> 0.
```

These two conditions extend the models to the free-lamp presentation and
send the established sofic-radical word to `-1` with constant-one error.

## Ideas and established structure (2026-08-14)

`notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md` replaces the two displayed
matrix conditions by exact algebra.  Write `N=M cap pi(Gamma)'` and
`N_t=M cap pi(t Gamma t^(-1))'` for a homomorphism into any finite tracial
`M`.

* The wall exists **iff** `N!=N_t` (`relative-wall-commutant-growth`).  The
  marked predecessor `h` is not data, and the Clifford strengthening is a
  self-adjoint involution in `N_t` anticommuting with its `Gamma`-conjugate
  (`compressed-commutant-majorana`).  Passing to the tracial matrix
  ultraproduct makes the finite endpoint and this exact endpoint the same
  question, so there is no rate-sensitivity in *existence*; the
  rate criterion of `FALSE_ONE_NUMBER_RELATIVE_COMMUTANT_CRITERION.md`
  governs only construction from imperfect data.
* The growth index `lambda(s)=[Ad pi(s)(N):N]` is multiplicative on the
  compressor semigroup, so a wall forces `[M:N]=infinity` and an infinite
  strictly increasing compressor tower
  (`compressor-growth-index-homomorphism`).
* Because `P_Gamma` contains the positive elementary transvections and the
  Steinberg identity is a relation inside it, a wall at a commutator
  compressor needs **infinite** index growth at a factor compressor
  (`commutator-compressor-carries-no-wall`).  This applies to the explicit
  Kun--Thom Theorem E pair and to this repository's explicit compressor
  `t=t_(u_12)`, since `u_12=[u_13,u_32]` with both factors nonnegative.
  Finite lamps over finite orbits are excluded.  The model-side mechanism
  is confirmed: `compressor-fixed-site-growth-infinite` proves that both
  `u_13` and `u_32` gain infinitely many `Gamma`-fixed sites, for every
  invariant graph, since the fixed-site set depends on the `G`-set alone.
* Any wall family stays flexibly far from the entire operator-norm
  asymptotic sector, not merely from exact representations
  (`wall-models-avoid-norm-microstates`).
* **Calibration.**  The normal form holds for an arbitrary target group, so
  it can be tested where the answer is known.  It is:
  `kun-thom-clifford-cover-weakly-sofic` proves the Clifford cover weakly
  sofic and nonsofic, so the entire algebraic content of this claim --
  involution, `Gamma_1`-centrality, anticommutation, surviving radical word
  -- is already realized in a metric ultraproduct of finite groups with
  bi-invariant metrics.  Hence no group-theoretic argument can refute this
  claim, and the only thing separating it from a solved problem is the
  metric.  The growth index is a genuinely tracial tool precisely because a
  metric ultraproduct of finite groups carries no Pimsner--Popa index.
* Under Alekseev--Thom Open Problem 6.2 the whole question becomes a demand
  on two nested exact coordinate centralizers
  (`wall-coordinate-reduction-under-at-op62`).

Dead ends recorded so they are not retried.

1. *Ore/positivity.*  `P_Gamma` generates `G` as a group but its own
   semigroup relations never write `1` as a nontrivial positive product, so
   one-sided inclusions cannot be reversed by fractions.  Commutators, not
   fractions, are the usable relations.  See
   `FALSE_COMPRESSION_SEMIGROUP_ORE_NO_GO.md`.
2. *Site relaxation.*  The Clifford normal form only asks the involution to
   centralize the compressed group `Gamma_1`, which looks weaker than the
   `Gamma<=K` condition of `FALSE_RELATIVE_BICOMMUTANT_ENDPOINT.md`
   `(RBE19)`.  It is not: conjugating the site subgroup by `t` returns the
   original condition, so the generalized-Bernoulli search space is
   unchanged.
3. *Semifinite comparison.*  In the tracial ultraproduct the Jones
   projection `e_N` and the compressor unitary `Ad pi(t)` do not lie in a
   common finite algebra -- `Ad pi(t)=u_t J u_t J` leaves the basic
   construction -- so the projection-comparison proof of the exact case has
   no direct analogue.  Only the index invariant survives, which is why
   `[M:N]=infinity` is the surviving necessary condition rather than a
   contradiction.
