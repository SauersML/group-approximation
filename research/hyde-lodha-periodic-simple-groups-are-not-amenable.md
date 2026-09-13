---
rg: 2
id: hyde-lodha-periodic-simple-groups-are-not-amenable
kind: claim
title: Hyde–Lodha's finitely presented simple group Q_2 of homeomorphisms of the line is not amenable
invalidates:
  - fp-simple-amenable-via-hyde-lodha-group
distinct_from:
  amenable-infinite-simple-circle-groups-fix-a-point: that is the general theorem for simple groups acting on the circle; this is a direct compression argument for one 1-periodic group of homeomorphisms of the line, using no simplicity
  lodha-moore-group-is-bi-orderable-and-not-lea: that concerns the Lodha–Moore group of piecewise projective homeomorphisms; this concerns the 1-periodic piecewise linear group of Hyde–Lodha
---

**ESTABLISHED.** Let `Γ_2 ≤ Homeo⁺(R)` be Hyde–Lodha's group (Definition 1.2 at
`n = 2`, `η = 6`) and `Q_2 = [Γ_2, Γ_2]`. Hyde–Lodha prove that `Q_2` is a finitely
presented simple group of orientation-preserving homeomorphisms of `R` (Theorem 1.3;
type `F_∞` by Theorem 4.8). It is infinite and torsion-free. Then `Q_2` is not
amenable, and neither is `Γ_2`.

**Why it matters.** `Q_2` is torsion-free, so it contains no copy of Thompson's `V`.
It is not a lattice in a product of trees, and none of the obstructions recorded
under `fp-infinite-simple-amenable-group` applied to it. It still cannot answer that
claim: the route `fp-simple-amenable-via-hyde-lodha-group` is dead.

**Mechanism.** Elements of `Γ_2` commute with `t -> t + 1`, so `Γ_2` acts on the
circle `R/Z`. The 1-periodic copy of `F_6'` inside `Q_2` pushes every compact arc of
`(0, 1)` off itself infinitely often, so an invariant probability measure is the
atom at `0`. Some element of `Q_2` moves `0`, a contradiction.

**Sources and scope.** The statements used were read as quoted in the repository's
Lean modules `GroupApproximation/GroupTheory/HydeLodha/` (`GammaTwo`,
`GammaTwoPeriodic`, `GammaTwoLambda`, `GammaTwoCoreMoves`, `PeriodicCore`,
`QTwoStatement`); the paper itself was not re-read in this lane, and its arXiv id is
not recorded here. The argument uses four printed inputs:
- 1-periodicity (Definition 1.2);
- the 1-periodic copy of `F_{η}` inside `Γ_n` (Proposition 1.4(2));
- an element `λ ∈ Γ_n` with `Z·λ != Z` (Proposition 3.4);
- transitivity of `F_η'` on each residue class of `Z[1/η] ∩ (0, 1)` modulo
  `(η - 1) Z[1/η]` (Proposition 3.5).
The quoted Definition 1.2, Proposition 1.4(2) and Proposition 3.4 are stated for
general `n`, so the same proof should cover every `Q_n`. Only `n = 2` is recorded as
established.

Route: `hyde-lodha-periodic-simple-groups-are-not-amenable-proof`.
