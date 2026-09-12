---
rg: 2
id: kt-step-nine-near-bound-from-counting-lift-proof
kind: route
title: Lift classes across eqToHom, estimate (7), and the same-cluster gap
target: kt-step-nine-near-bound-from-counting-lift
requires: []
artifacts:
  - GroupApproximation/KunThom/StepNineNear.lean
---

## Direct proof, machine-checked

- **Align the indices.**
  - Rewrite `π i` to `x` in the goal, and substitute the image `i` of `x`.
  - Destructure the target object of the lift, and substitute `b x = y`, read off
    the equation `e` with `Obj.val`.
- **The lifted arrow.** The arrow `g` is the class of a representative `ρ₀`.
  - `comp_eqToHom_heq` and `hg₂` give `b.hom x = ⟦ρ₀⟧`.
  - So `Quotient.out_eq` makes the chosen representative of `b` at `x` related to `ρ₀`.
- **Estimate (7).** Take `θ`, a representative of `F` of that class.
  - `h7` bounds `θ` against the raw map on the representative of `b` at `x` by `ε`.
- **The image class.**
  - The class of `θ` is `(F ⋙ K)` of the class of `ρ₀`, by `congrArg` along the
    inclusion functor.
  - By `hg₁` and `comp_eqToHom_heq`, that class agrees with the arrow of `â` at `i`
    after the object equality from `h₁`.
- **The gap.** `ClusterMetric.twoSidedDisagreement_lt_of_heq_ofRep` substitutes the
  object equality, reads the classes as equal, and applies `lt_of_rel` and the
  triangle inequality. The chosen representative of `â` at `i` is within
  `radius + ε` of the raw map.
- **One-sided.** The disagreement card is at most the two-sided disagreement.

Probe GREEN at base 19b046f71, tag 0912-142824-37886. The three printed axiom
closures lie within `[propext, Classical.choice, Quot.sound]`.
