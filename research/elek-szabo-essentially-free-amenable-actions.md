---
rg: 2
id: elek-szabo-essentially-free-amenable-actions
kind: claim
title: Essentially free amenable actions have a Følner and a non-paradoxical characterization, exist for amenable and residually finite groups, force residual finiteness under property (T), and are obstructed by one characteristic subgroup (Elek–Szabó 2005)
distinct_from:
  mean-free-amenable-actions-residually-amenable-and-sofic: that proves the residually amenable case, heredity, soficity and the amenable-stabilizer transfer in this graph's notation; this imports the source where the notion, the Følner characterization and the finite-quotient construction first appear.
  kazhdan-groups-mean-free-amenable-iff-residually-finite: that proves the same equivalence inside this graph; this pins its earlier statement, Proposition 4.4 of the source.
  elek-szabo-sofic-permanence: that is Theorem 1 of the 2003/2006 paper On sofic groups; this is Sections 1.4, 4 and 5 of the 2005 Math. Ann. paper.
---

**ESTABLISHED** (literature import).

**Source.** G. Elek and E. Szabó, *Hyperlinearity, essentially free actions and L²-invariants. The sofic
property*, Math. Ann. 332 (2005), no. 2, 421–441; arXiv:math/0408400. Transcribed from the arXiv PDF;
see the route for how it was read.

**Terminology bridge.** Their "Γ-invariant finitely additive (probability) measure on X" is an invariant
mean on `ℓ∞(X)` evaluated on indicators. So an *essentially free amenable action* is exactly a
*mean-free amenable action* in `mean-free-amenable-actions-residually-amenable-and-sofic`.

**Verbatim.**
- §1.4, **Definition 1.3**: "An amenable action of a group Γ on a set X is called essentially free if
  there exists a Γ-invariant finitely additive measure µ on X such that for any 1 ≠ g ∈ Γ,
  µ(Fix(g)) = 0, where Fix(g) ⊆ X denotes the fixed point set of g."
- §4, **Theorem 3**: "Let Γ be a group acting on a set X. For elements g ∈ Γ we denote by Fix(g|X) ⊆ X
  the fixed point set of g in X. Then the following conditions are equivalent:
  1. The action is an essentially free amenable action.
  2. The action is non-paradoxical in the following sense: X cannot be written as a union of subsets
     X = A1 ∪ A2 ∪ . . . ∪ Al ∪ B1 ∪ B2 ∪ . . . ∪ Bm such that (a) for some group elements
     g1, h1, g2, h2, . . . , gl, hl ∈ Γ the subsets g1A1, h1A1, g2A2, h2A2, . . ., glAl, hlAl are pairwise
     disjoint, (b) for each Bi there are elements pi ∈ Γ with Bi = Fix(pi|X).
  3. For any finite subset K ⊆ Γ and any number ε > 0 there exists a finite subset F ⊆ X such that
     (a) |gF △ F|/|F| < ε for any g ∈ K, (b) |Fix(g|X) ∩ F|/|F| < ε for any g ∈ K."

  (As printed, 3(b) reads "for any g ∈ K"; it can only hold for `g ≠ 1`.)
- §4, **Corollary 4.2**: "Let Γ be a discrete group. Then Γ has an essentially free almost-action if and
  only if Γ is sofic." Almost-actions are Definitions 1.4–1.5 of the source: bijections `φ(g)`
  preserving µ and multiplicative off µ-null sets.
- §4, **Proposition 4.3**: "If Γ is amenable or residually finite then it has an essentially free
  amenable action."
- §4, **Proposition 4.4**: "Let Γ be a discrete group of Kazhdan's Property (T). Then Γ has an
  essentially free amenable action if and only if it is residually finite."
- §5, setup: "Let (Γ, X, µ) be an action of a group Γ on a set X with a Γ-invariant finitely additive
  measure µ. We denote the class of such actions by InvΓ. Let NΓ,X,µ be the set of elements g ∈ Γ such
  that µ(Fix(g|X)) = 1. Then NΓ,X,µ is a normal subgroup of Γ. [...] Let NΓ = ⋂ over (Γ,X,µ) ∈ InvΓ of
  NΓ,X,µ, this is a characteristic subgroup in Γ."
- §5, **Proposition 5.1**: "Let Γ be a group.
  1. There is an action (Γ, X, µ) ∈ InvΓ such that µ(Fix(g|X)) = 1 for g ∈ NΓ, 0 for g ∈ Γ \ NΓ.
  2. Γ has an essentially free amenable action on a set X if and only if NΓ = 1.
  3. Γ/NΓ is a sofic group."

**Priority note.** In this graph:
- `mean-free-amenable-actions-residually-amenable-and-sofic` items 1 and 3 extend Proposition 4.3 and
  the direction (1) ⇒ (3) of Theorem 3;
- `kazhdan-groups-mean-free-amenable-iff-residually-finite` restates Proposition 4.4.

Both nodes already disclaim novelty, but neither cites this source.

DERIVATION
elek-szabo-essentially-free-amenable-actions-citation
