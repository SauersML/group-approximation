---
rg: 2
id: f2xf2-on-dyadic-lattice-quotient-bounds-vertex-action
kind: claim
title: The right action of a Fuchsian-times-2-adic free lattice pair on the dyadic S-arithmetic quotient is an explicit F2 x F2 candidate controlling the vertex action
distinct_from:
  f2xf2-admits-nonsofic-action: that asks for any essentially free nonsofic action of F2 x F2; this names one explicit homogeneous action whose nonsoficity follows from nonsoficity of the dyadic vertex action and whose soficity implies soficity of that action.
  dyadic-vertex-soficity-equals-frame-dynamics-soficity: that is an equivalence on the 2-adic face; this passes to the dual action of a reducible lattice by lattice duality, and one direction is lost at a product factor.
  product-tree-lattices-in-paunescu-class-iff-f2xf2: that concerns all actions of tree-product lattices at once; this is one algebraic action of a Fuchsian free group times a 2-adic free group on an S-arithmetic quotient.
---

**ESTABLISHED (unreviewed).** Put `H = PSL_2(R) × PSL_2(Q_2)`, `A = PSL_2(Z[1/2])` (a lattice in
`H`), `Γ(2) <= PSL_2(Z)` the free principal congruence subgroup, and `Λ <= PSL_2(Q_2)` a
torsion-free cocompact lattice, free of rank `r >= 2`. Let

```text
Λ'' = Γ(2) × Λ ≅ F_2 × F_r,        X_A = A\H with Haar probability,
(Ah)·(γ, λ) = A h (γ, λ).                                               (FF1)
```

1. `(FF1)` is an essentially free p.m.p. action. It is stably orbit equivalent to the diagonal
   left action `A ↷ H/Λ'' = PSL_2(R)/Γ(2) × PSL_2(Q_2)/Λ`, which has the frame dynamics
   `A ↷ PSL_2(Q_2)/Λ` as a factor.
2. If `(FF1)` is sofic, the dyadic vertex action `A ↷ A/PSL_2(Z)` is sofic.
3. If the dyadic vertex action is not sofic, `(FF1)` is an essentially free nonsofic action of
   `F_2 × F_r`. Inducing to the finite-index overgroup `F_2 × F_2` then gives an essentially free
   nonsofic action of `F_2 × F_2`.

**Why record it.** `f2xf2-nonsofic-action-from-nonsofic-dyadic-vertex-action` transfers
nonsoficity through an abstract coupling with a Bernoulli twist. Here the candidate is concrete and
algebraic. The discrete Fuchsian group `Γ(2)` translates the real coordinate of the S-arithmetic
quotient, and the free `2`-adic lattice `Λ` translates the tree coordinate. The two actions commute,
each alone is an action of a free group and hence sofic, and their joint soficity bounds the dyadic
vertex question from above. Conversely, a positive answer to the vertex question does not obviously
make `(FF1)` sofic, because soficity does not in general pass to extensions such as the extra factor
`PSL_2(R)/Γ(2)`.

**Model test (calibration only).** Two replacements have finite orbits. Replacing `A` by `Λ''`
gives the right action of `Λ''` on `Λ''\H`, whose finite orbits are the Hecke points. Replacing
`Λ''` by `A` gives `A ↷ H/A`, with finite Hecke orbits and no separating `K`-orbit label. With
equidistribution, such systems are sofic by `finite-equidistributed-orbits-give-sofic-action`;
equidistribution is not imported here. In `(FF1)` the lattices `A` (irreducible) and `Λ''`
(reducible) are not commensurable, so no orbit is finite. The action is genuinely approximate, and
the finite-orbit method is unavailable.

Proof in `f2xf2-on-dyadic-lattice-quotient-bounds-vertex-action-proof`.
