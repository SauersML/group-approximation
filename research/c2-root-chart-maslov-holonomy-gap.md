---
rg: 2
id: c2-root-chart-maslov-holonomy-gap
kind: claim
title: Chordal C2 root charts leave a single Maslov holonomy cycle with positive HS energy
refuted_by: c2-root-commuting-cycle-is-maslov-trivial
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
distinct_from:
  atlas-a4-four-cycle-dirichlet-compiler: that compiles an A4 context atlas to a scalar four-transvection Dirichlet energy; this uses the C2 symplectic root system and requires the surviving cycle to carry the mod-three Meyer--Maslov cocycle.
  iwahori-uniform-infinitesimal-rigidity: that seeks a Jacobian gap for two SL2(Z) vertices glued along an Iwahori subgroup; this exactifies abelian root charts by chordality and isolates one rank-two projective holonomy cycle.
---

Construct a finite root-subgroup presentation of `Sp_4(Z)` adapted to the
mod-three Deligne/Meyer--Maslov multiplier such that:

1. all commuting-root relations can be covered by finitely many chordal
   induced graph-product charts;
2. after same-dimension HS exactification on those charts and synchronization
   on overlaps, all projective curvature is gauge-equivalent to one bounded
   family of induced non-chordal `C2` cycles;
3. a nontrivial mod-three Maslov holonomy on one of those cycles has a
   dimension-free positive normalized-HS relator-energy cost.

## Attempts

- **Compute before proving.** Enumerate a concrete Steinberg/Chevalley
  presentation of type `C2`, its root-commutation graph, and minimal chordal
  covers.  Push the cocycle by explicit coboundaries and verify that its
  support cannot be removed from the non-chordal residue.
- **Use Spaas only locally.** `chordal-abelian-graph-products-hs-stable` is
  meant to erase commuting charts, not to claim the whole symplectic group is
  a chordal graph product.
- **Holonomy payment.** Once all chart relations are exact, the remaining
  variables should live in overlap commutants.  The analytic payment is now
  established by `positive-cycle-near-unitary-edges-force-trivial-holonomy`:
  a positive block cycle whose edges are near unitaries forces their product
  near the identity, with a dimension-free bound.  What remains is to
  synchronize the chordal lifts into that single positive cycle kernel and
  identify its edge product with the order-three Maslov scalar.
- **Falsification.** If a coboundary gauge moves the entire mod-three cocycle
  into chordal charts, or if the overlap commutants admit stationary phase
  flow with vanishing energy, this compiler does not prove the desired gap.

## REFUTED (2026-08-21)

The proposed nonchordal cycle exists, but it carries no Deligne curvature.
Kassel's explicit eight-root Steinberg presentation shows that the commuting
graph has four maximal triangular charts and one induced four-cycle on the
long roots.  The canonical root generators lift **all twelve commuting
edges simultaneously** to the Steinberg cover.  Thus the map from the whole
root graph product to `Sp4(Z)` lifts through the Deligne three-cover, and the
multiplier is already a coboundary on the whole nonchordal graph product.
See `c2-root-commuting-cycle-is-maslov-trivial`.

The central generator is the rank-one Weyl word `w_gamma^4`; comparing its
long-root realizations uses noncommuting Chevalley relations.  Those relations
are not controlled by chordal abelian graph-product stability.  Therefore the
positive-cycle inequality remains correct, but this root-commuting chart
compiler cannot supply it with a cycle whose edge product is the nontrivial
Maslov scalar.
