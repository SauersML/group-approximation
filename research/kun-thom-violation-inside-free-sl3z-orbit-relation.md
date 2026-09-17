---
rg: 2
id: kun-thom-violation-inside-free-sl3z-orbit-relation
kind: claim
title: Some free SL3(Z)-action has a Kazhdan infranormal pair in its full group whose fixed algebra is not invariant
distinct_from:
  groups-containing-kun-thom-pair-have-nonsofic-actions: that needs the pair inside the group; here it sits only in the full group of an action, as piecewise SL3(Z) elements
  free-action-containing-nonsofic-group-relation-is-nonsofic: that needs a free action of a nonsofic group inside the relation; here the pair may act non-freely, and its violation is the obstruction
---

**OPEN.** There exist:

* a free p.m.p. action `a = SL_3(Z) ↷ (X, μ)`;
* countable subgroups `Γ ≤ H ≤ [R_a]` with property (T), where `Γ` is infranormal in `H`;

such that `L^∞(X)^Γ` is not `H`-invariant.

**Equivalent form.** There exist:

* a p.m.p. action `b` of a Kazhdan group `H` with an infranormal Kazhdan subgroup `Γ`, and a non-invariant
  `L^∞^Γ`;
* a free p.m.p. `SL_3(Z)`-action `a` on the same space, with `R_b ⊆ R_a`.

Then `b(h)x = c(h,x)·x` for the cocycle `c : H × X → SL_3(Z)` of `b` into the free action `a`.

**Colouring form of non-invariance.** `L^∞^Γ` fails to be `H`-invariant iff `b` factors onto an `H`-invariant random
colouring `ξ ∈ {0,1}^{H/Γ}` that is not a.s. constant on `Γ`-orbits of cosets. Given a `Γ`-invariant set `E`, put
`ξ(x)(hΓ) = 1_{hE}(x)`. This is well defined because `hγE = hE`, and it is `H`-equivariant. Conversely, take `E = {ξ(Γ) = 1}`.

By `full-group-kazhdan-pairs-have-invariant-fixed-algebras`, a witness shows that `a` is not sofic, and hence
`sl3z-admits-nonsofic-action`. Because `𝒮` is measure-equivalence invariant, `SL_3(Z)` may be replaced by any
lattice of `SL_3(R)`, restricting the relation to a positive-measure set.

Seeds already ruled out are listed in `sl3z-nonsofic-from-full-group-kun-thom-violation`.

## Attempts

* **Seed classes (sw-088, 2026-09-17).** Three seed classes die, recorded in
  `sl3z-nonsofic-from-full-group-kun-thom-violation`: finite `Γ`-orbits (unconditional), constant cocycles
  `c(h,x) = ρ(h)` (they need a non-normal infranormal Kazhdan pair inside `SL_3(Z)`), and untwistable cocycles with an
  ergodic infinite torsion abelian subgroup (sketch, via Popa superrigidity for generalized Bernoulli seeds). Dies
  at: no non-malleable Kazhdan-pair action with a non-constant cocycle into `SL_3(Z)` is recorded, and no cocycle
  superrigidity theorem for such actions is imported.
