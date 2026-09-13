---
rg: 2
id: mikhailova-coset-action-two-sided-proof
kind: route
title: Direct computation of the coset space and pullback soficity from an amenable base
target: mikhailova-coset-action-is-two-sided-q-action
requires:
  - gkp-amenable-group-actions-are-sofic
  - gkp-sofic-action-toolkit
artifacts: []
---

The identification (TS) is a direct computation. The two soficity facts are
GKP Theorem 2.17 and the pullback observation (GKP Proposition 2.15(1) in the
surjective case), both required above.

## The identification (TS)

Define `Psi : F x F -> Q` by `Psi(a,b) = phi(a) phi(b)^(-1)`.  It is onto since
`phi` is onto.  For `(a,b),(a',b') in F x F`,

```text
Psi(a,b) = Psi(a',b')
  <=> phi(a) phi(b)^(-1) = phi(a') phi(b')^(-1)
  <=> phi(a'^(-1) a) = phi(b'^(-1) b)
  <=> (a'^(-1)a, b'^(-1)b) in M
  <=> (a',b')^(-1)(a,b) in M
  <=> (a,b) in (a',b') M.
```

So `Psi` descends to a bijection `(F x F)/M -> Q`.  Equivariance:

```text
Psi((g,h)(a,b)) = Psi(ga, hb) = phi(g) phi(a) phi(b)^(-1) phi(h)^(-1)
               = phi(g) * Psi(a,b) * phi(h)^(-1),
```

which is (TS).  The stabilizer of `1 = Psi(1,1)` is
`{(g,h) : phi(g) phi(h)^(-1) = 1} = {(g,h) : phi(g)=phi(h)} = M`.  Under `Psi`,
(TS) is the two-sided translation action of `Q x Q` on `Q = (Q x Q)/Delta Q`
precomposed with `phi x phi : F x F -> Q x Q`.  `∎`

## Soficity for an amenable base

Two inputs.

1. **Every action of an amenable group on a set is sofic.** This is GKP
   Theorem 2.17 ([[gkp-amenable-group-actions-are-sofic]]). Apply it with the
   amenable group `P = Q x Q` acting on `Y = Q`: the two-sided action
   `Q x Q curvearrowright Q` is sofic.

   *Correction (2026-09-13, lane `ex2-free-wreath-amenable-sofic`).* An earlier
   version justified this item by "an invariant mean pushes forward, so the
   action is amenable, and amenable actions are sofic (finite
   orbit-approximations from Følner sets)". The last step is false for
   non-amenable actors: [[amenable-action-of-a-sofic-group-need-not-be-sofic]]
   gives an amenable action of a sofic group that is not sofic. The conclusion
   of this item still holds, because here the actor `Q x Q` is itself amenable.

2. **Soficity of a set-action is preserved under pullback along a group
   homomorphism.**  If `rho : G' -> G` is a homomorphism and `alpha : G ↷ Y`
   is sofic, then `alpha compose rho : G' ↷ Y` is sofic: a finite
   `(F, E, epsilon)`-orbit approximation `Phi : G -> Sym(A)` of `alpha`
   composes with `rho` to a `(rho^(-1)(F), E, epsilon)`-orbit approximation
   `Phi compose rho` of `alpha compose rho`, and unital
   `epsilon`-multiplicativity is preserved because `rho` is a homomorphism.
   For surjective `rho` this is GKP Proposition 2.15(1)
   ([[gkp-sofic-action-toolkit]]).

Combining, with `rho = phi x phi` and `alpha` the two-sided action, the coset
action `F x F curvearrowright (F x F)/M ~= Q` is sofic whenever `Q` is
amenable.  Non-separability of `M` (equivalently, undecidability of the word
problem of `Q`) plays no role here: it obstructs residual finiteness and
finite-quotient models, not soficity of the action.  `∎`

## The natural dividing line is the base (recorded, not needed above)

Restricting (TS) to `F x 1` gives the pullback along `phi` of the left-regular
action `Q curvearrowright Q`, and a sofic action restricts to a sofic action of
any subgroup.  So the coset action being sofic entails soficity of that
pullback subaction.  The left-regular action of `Q` being sofic is a standard
characterisation of `Q` sofic. Whether soficity of its pullback along the
surjection `phi` descends to `Q` itself is not asserted here (the finite
`F`-models need not respect `ker phi`); by GKP Theorem 2.19 the pullback to the
free group `F` alone is always sofic. The sufficient direction extends beyond
amenable bases: a residually amenable base makes the coset action sofic
([[separating-sofic-quotient-sets-make-an-action-sofic]], (C3)). For the
compiler's own base, the Higman host, the question is open
([[compiler-rope-edge-is-not-co-amenable]], (R3)).
