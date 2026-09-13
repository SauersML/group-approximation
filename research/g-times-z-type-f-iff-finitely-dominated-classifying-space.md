---
rg: 2
id: g-times-z-type-f-iff-finitely-dominated-classifying-space
kind: claim
title: "G x Z is of type F exactly when K(G,1) is finitely dominated"
distinct_from:
  g-times-z-type-f-iff-g-f-infinity-with-finite-cd: that identifies the groups with G x Z of type F algebraically, as the groups of type F_infinity with finite cd or equivalently the finitely presented groups of type FP; this identifies them topologically, as the groups with a finitely dominated classifying space, which turns Problem 1.21 into Wall's finiteness question for aspherical complexes.
  fp-type-fp-group-is-type-f-iff-wall-class-vanishes: that equates type F with vanishing of the algebraic Wall class for finitely presented groups of type FP; this equates G x Z being of type F with finite domination of K(G,1), the setting of Wall's topological finiteness obstruction.
---

For a group `G`, `G × Z` is of type F if and only if some, equivalently
every, `K(G,1)` CW complex is finitely dominated: there are a finite CW
complex `K` and maps `f : K(G,1) → K`, `g : K → K(G,1)` with `g ∘ f ≃ id`.

Consequently Zaremsky's Problem 1.21
(`zaremsky-1-21-g-times-z-type-f-implies-g-type-f`) asks exactly this: is every
finitely dominated aspherical CW complex homotopy equivalent to a finite CW
complex? Aspherical CW complexes are the `K(G,1)`s. By Wall's theorem the
only obstruction is Wall's finiteness obstruction of `K(G,1)`. Up to sign,
it is the class `σ(G)` of
[[fp-type-fp-group-is-type-f-iff-wall-class-vanishes]].

The route [[g-times-z-type-f-iff-finitely-dominated-classifying-space-proof]]
proves this with Mather's trick and Wall's criterion (Ferry–Ranicki,
arXiv:math/0008070, Proposition 1.5 and Theorem 3.1). It also re-derives,
from the topological side, the equivalence with "finitely presented of type
FP" and "type `F_∞` with finite cd". The algebraic proofs of those are in
[[g-times-z-type-f-iff-g-f-infinity-with-finite-cd]].
