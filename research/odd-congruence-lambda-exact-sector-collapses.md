---
rg: 2
id: odd-congruence-lambda-exact-sector-collapses
kind: claim
title: The three-term Weyl relation collapses the whole odd-congruence Lambda-exact sector at rank two
distinct_from:
  odd-congruence-exact-sector-is-one-inner-action: that reduced the sector to the triviality of one inner action and killed only translation-type correctors; this closes the sector outright — the corrector is forced to be exactly 1 by the three-term Weyl-orbit relation, for EVERY admissible W.
  odd-congruence-vertex-sector-admits-no-exact-leak: that closes the odd sector for the exact SL_2 profile via the normal-closure squeeze in the amalgam; this is the SL_3 statement, proved by a mechanism (rank-two Weyl rigidity) that does not exist at SL_2, and it yields the FULL collapse in the sector, not one profile's exclusion.
  single-hecke-average-isometry-for-lambda-central-unitaries: that is the full collapse over all regular-trace models; this proves it on the Lambda-exact odd-congruence sector, so the surviving enemy must have Lambda-microstates at uniform distance from every exact representation — the uniform-outlier sector shared with the Iwahori and HS-Dehn far-sector residues.
---

Let `Gamma = SL_3(Z[1/p])`, `Lambda = SL_3(Z)`, `h = diag(p, 1,
p^(-1))`.  Call `pi : Gamma -> U(M)` (tracial matrix ultraproduct,
trace-preserving) **Lambda-exact of odd congruence type** if it has
microstates whose `Lambda`-restrictions are genuine
finite-dimensional unitary representations `sigma_m`, necessarily
factoring through `SL_3(Z/n_m)` (superrigidity + CSP), with `n_m`
coprime to `2p`.  THEOREM: in this sector the collapse holds
unconditionally —

```text
pi(Lambda)' cap M = pi(Gamma)' cap M,                            (OS1)
```

with no regular-trace hypothesis and no restriction on the
multiplicities of `sigma_m`.  Consequently no leak, no enemy
character and no failure of the single-average isometry can live over
`Lambda`-exact odd-congruence microstates, and the surviving enemy
sector for `(RC3)` is exactly: `Lambda`-restrictions at UNIFORM
positive distance from every exact representation of `SL_3(Z)`.

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

- **Why this does not close the wall.**  `SL_3(Z)` is an infinite
  property (T) hyperlinear group, hence not flexibly HS-stable, so
  approximate representations of `Lambda` far from every exact one
  EXIST and the sector is proper.  The theorem converts the open
  collapse into: no leak over uniformly-non-correctable
  `Lambda`-microstates — aligning the last open sector of this lane
  exactly with the uniform-outlier residues of
  `iwahori-outlier-repair` and the HS-Dehn far sector, and giving
  the outlier sector a new necessary feature: the obstruction to
  correcting the enemy's `Lambda`-microstates must survive the
  property (T) conjugation-lifting used here, i.e. it is a
  representation-variety outlier, not a commutant artifact.
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
  evidence: warm starts on exact `Lambda`-models sit INSIDE the
  closed sector, where no enemy exists at all; only searches that
  hold the `Lambda`-part at definite distance from all exact models
  probe the live sector, which is the correct design for the next
  probe generation.
