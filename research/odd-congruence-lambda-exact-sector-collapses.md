---
rg: 2
id: odd-congruence-lambda-exact-sector-collapses
kind: claim
title: The three-term Weyl relation collapses the whole odd-congruence Lambda-exact sector at rank two
distinct_from:
  odd-congruence-exact-sector-is-one-inner-action: that reduced the sector to the triviality of one inner action and killed only translation-type correctors; this closes the sector outright — the corrector is forced to be exactly 1 by the three-term Weyl-orbit relation, for EVERY admissible W.
  odd-congruence-vertex-sector-admits-no-exact-leak: that closes the odd sector for the exact SL_2 profile via the normal-closure squeeze in the amalgam; this is the SL_3 statement, proved by a mechanism (rank-two Weyl rigidity) that does not exist at SL_2, and it yields the FULL collapse in the sector, not one profile's exclusion.
  single-hecke-average-isometry-for-lambda-central-unitaries: That is the full collapse over all regular-trace models; this proves it only on the exact lattice sector at levels coprime to the localization prime, leaving other primary sectors and uncorrected lattice tuples untreated.
---

Let `Gamma = SL_3(Z[1/p])`, `Lambda = SL_3(Z)`, `h = diag(p, 1,
p^(-1))`.  Call `pi : Gamma -> U(M)` (tracial matrix ultraproduct,
trace-preserving) **Lambda-exact of odd congruence type** if it has
microstates whose `Lambda`-restrictions are genuine
finite-dimensional unitary representations `sigma_m`, necessarily
factoring through `SL_3(Z/n_m)` (superrigidity + CSP), with `n_m`
coprime to `p`.  (Strengthened 2026-08-21, second pass: the proof
uses only invertibility of `p` mod `n_m` — nothing needs `n_m` odd
beyond the `p = 2` instance, where the two conditions coincide; for
odd `p` the closed sector includes all 2-power levels.)  THEOREM: in
this sector the collapse holds unconditionally —

```text
pi(Lambda)' cap M = pi(Gamma)' cap M,                            (OS1)
```

with no regular-trace hypothesis and no restriction on the
multiplicities of `sigma_m`.  Consequently no leak, no enemy
character and no failure of the single-average isometry can live over
`Lambda`-exact coprime-congruence microstates. This conclusion does
not cover exact representations at arbitrary primary levels or general
approximate lattice representations.

Mechanism (rank two is essential).  The exact slot `V'` (the
congruence image of `h`) commutes with the full commutant tower; the
corrector `W = V'^* V` lands in that tower by property (T) lifting;
and the Weyl-orbit relations of the diagonal —

```text
w_13 h w_13^(-1) = h^(-1),
h' = h h''^(-1)   (h' = w_12 h w_12^(-1), h'' = w_23 h w_23^(-1)),
```

— evaluate, after the commutations, to `W^2 = 1` and then `W = 1`
EXACTLY.  At `SL_2` the diagonal has a single Weyl direction, only
`W^2 = 1` survives, and the involution corrector is precisely the
known `BS(1,4)`-plus-one-involution enemy seed of the Iwahori lane:
the three-term relation is the rank-two rigidity that `SL_2` lacks,
the group-theoretic analogue of needing two multiplicatively
independent maps in Furstenberg-type measure rigidity
(`far-sector-is-solenoid-measure-rigidity`).

## Attempts

- **Why this does not close the wall.** Infinite hyperlinear
  property-(T) groups fail strict HS stability; this does not imply
  failure of flexible HS stability. Flexible stability of `SL_3(Z)`
  remains the separate open claim `sl3-z-weakly-ucp-stable`.
  The present theorem starts with exact coprime lattice coordinates.
  It supplies no correction of arbitrary lattice microstates and
  leaves the other primary exact sectors subject to their own
  partial results. It therefore does not identify the full residual
  with flexible-stability outliers.
- **Mixed levels: what survives is a two-adic Iwahori intertwining
  (2026-08-21 analysis).**  For `Lambda`-exact microstates at MIXED
  levels `n = 2^a q` (`q` odd), `G_n = SL_3(Z/2^a) x SL_3(Z/q)` and
  the exact slot can be chosen as `V' = sigma(1, h_q)`; the corrector
  `W = V'^* V` then intertwines the images of the two parahorics
  `Lambda_-` and `Lambda_+ = Lambda cap h Lambda h^(-1)` ON THE
  2-PART while the Weyl evaluation no longer closes (it used
  `[W, pi(w)] = 0`, which needed the full commutant).  So the general
  `Lambda`-exact sector reduces to a pure 2-adic tower problem — an
  `SL_3` Iwahori-type compatibility question at the prime `2`,
  the exact higher-rank sibling of the `B_+/B_-` diagram in
  Dogon--Vigdorovich Question 1.4 — matching yet again the doctrine
  that the enemy is pinned to the prime two.  Formalizing this
  reduction (and testing whether a residual Weyl constraint pins the
  2-part corrector to the finitely many level-4 blocks) is the next
  theorem slot in this lane.
- **Interaction with the probes.**  The probe floor
  (`experiments/hecke42_average_probe.py`: everything collapses to
  the isometry) is now half-explained by theorem rather than
  evidence: warm starts on exact coprime `Lambda`-models sit inside
  the closed sector. Other primary exact models and general
  approximate lattice tuples require their separate analyses.
- **The p-adic tower residue is now quantitatively bounded (2026-08-25).**
  `lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible` proves, for
  every prime `p`, that a `Lambda`-exact microstate of level `p^D m'` with
  `h`-twist defect `epsilon` on the Kazhdan subgroup `C_0` has `p`-divisible
  weight at most `12 D epsilon/(c_p kappa_0)`, `c_p > 0` explicit.  So the
  mixed-level sector above either collapses to the coprime sector (closed
  here) up to negligible weight, or its `p`-adic depth exceeds
  `c_p kappa_0/(12 epsilon)`: the residual enemy is an ultra-deep tower.
  The mechanism is the Atkin--Lehner-type twist `J h^D` transported by one
  Kazhdan projection; it does not use the exact slot, so it applies at the
  prime `2` as well (with the weakest constant, `c_2 = 2/21`), and the
  constants improve with `p` -- the pair is prime-generic, so the lane is not
  pinned to `p = 2` by this residue.
- **Arbitrary matrix carriers on the coprime face are now excluded
  (2026-09-08).** `sl3-re-coprime-face-from-kazhdan-carrier-control`
  uses the exact slot together with uniform Kazhdan control of its
  distance to any matrix subalgebra. The independent route
  `sl3-re-coprime-face-closes-by-jones-kazhdan` applies the same gap
  on the Jones basic construction. Both close
  `sl3-re-lambda-exact-coprime-face-is-unfaithful` without the earlier
  logarithmic containment-rate assumption. The false identification
  of the moving slot with an element of `pi(Lambda)''` remains
  withdrawn.
