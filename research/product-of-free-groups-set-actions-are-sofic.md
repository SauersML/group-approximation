---
rg: 2
id: product-of-free-groups-set-actions-are-sofic
kind: claim
title: Every action of a product of two free groups on a countable set is sofic
distinct_from:
  f2xf2-in-paunescu-class: that asks whether every p.m.p. action of F2 x F2 is sofic in Paunescu's sense; this asks it for actions on countable sets in the GKP sense, and the only recorded link between the two notions is GKP Proposition 4.1 for generalized Bernoulli shifts.
  gkp-free-group-actions-are-sofic: that is GKP Theorem 2.19 for a single free group; this asks whether two commuting free factors can always be modelled together.
  compiler-rope-is-coset-wreath-of-an-a-t-menable-base: that conjectures in prose that coset actions of residually finite a-T-menable groups are sofic; this is the product-of-free-groups case, which is all the compiler rope needs.
---

OPEN. Let `F` and `F'` be countable free groups. Every action
`F x F' ↷ X` on a countable set is sofic, in the sense of GKP Definition
2.1(5).

**What it would give.** Every Mikhailova rope `< F x F, v | [v, M_Q] = 1 >`
over every finitely presented `Q` would be sofic, by GKP Theorem 3.7. The
compiler's first rope `Gamma_e` would be sofic on every branch
([[compiler-rope-edge-is-not-co-amenable]], (R3)). The route is
[[rope-separation-from-product-free-group-set-actions]].

**Equivalent form.** By
[[product-free-set-actions-reduce-to-left-right-actions]], this holds iff
every countable group is left-right sofic, iff (MLF1) is sofic for every
finitely presented group. That is
[[every-countable-group-is-left-right-sofic]]; routes run both ways.

**What is known.**

- A single free factor acts soficly (GKP Theorem 2.19).
- If the stabilizer is a Mikhailova subgroup `M_Q` with `Q` residually
  amenable, the action is sofic
  ([[separating-sofic-quotient-sets-make-an-action-sofic]], (C3)). So is any
  amenable transitive action whose stabilizer acts soficly
  ([[co-amenable-induction-of-sofic-actions]]).
- For general actors, commuting sofic actions need not combine to a sofic
  action ([[commuting-sofic-actions-need-not-combine]], GKP Question 4.2).
  Amenable actions need not be sofic
  ([[amenable-action-of-a-sofic-group-need-not-be-sofic]]). Both
  counterexamples use a Kazhdan actor.
- An orbit is sofic whenever its stabilizer meets `F x 1` or `1 x F'` in an
  amenably separable subgroup
  ([[g-x-free-set-actions-sofic-when-kernel-amenably-separable]]).
- An orbit is sofic whenever every finitely generated subgroup of the Goursat
  quotient of its stabilizer is left-right sofic
  ([[product-free-set-actions-reduce-to-left-right-actions]]). The left-right
  sofic groups include every LEA group, and are closed under co-amenable
  overgroups ([[left-right-sofic-closed-under-co-amenable-overgroups]]).

## Attempts

- **Kun--Thom obstruction (dies as an obstruction).** Rigidity of that kind
  needs an infinite Kazhdan subgroup of the actor. `F x F'` has the Haagerup
  property, so it has none. A counterexample would be nonsoficity of a set
  action without property (T) behind it.
- **Transitive reduction and Goursat (partial).** By GKP Propositions 2.15(2)
  and 2.16 it suffices to treat `X = (F x F')/L`. Goursat's lemma writes `L` as
  a fibre product over an isomorphism `p_1(L)/N_1 ~= p_2(L)/N_2 =: Q`, where
  `N_1 x 1 = L ∩ (F x 1)` and `1 x N_2 = L ∩ (1 x F')`. When `p_1(L) = F` and
  `p_2(L) = F'`, `X` is the two-sided coset space of `Q`, pulled back. (C3)
  handles residually amenable `Q`. A finite group `K` receiving a partial
  embedding of a ball of `Q` also gives an exact model on `K x K`, with labels
  `pi_(k,k')(q) = k^-1 psi(q) k'`. But the labelling condition forces the
  bounded relators of `Q` to hold in `K`, so this is local embeddability into
  finite groups, which for finitely presented `Q` is residual finiteness. Every
  model built so far factors through amenable or finite quotients of `Q`. The
  compiler needs `Q` equal to a Higman host, and that case is not handled.
  *Completed 2026-09-13 (lane ex3-pfg-positive):* non-full projections reduce
  to full ones over finitely generated subgroups of `Q`, by a Marshall Hall
  retraction, finite-index induction and local separation
  ([[product-free-set-actions-reduce-to-left-right-actions]]).
- **Free completion (dies as stated).** GKP's proof of Theorem 2.19 extends the
  partial permutations of a finite piece of `X` to permutations, one free
  generator at a time. For `F x F'` the left and right generators must also
  commute. Two families of partial permutations that commute where defined
  need not extend to commuting permutations, and no extension procedure is
  known that keeps the labelled local picture required by Definition 2.1(3).
- **Through soficity of `Q` (not known to work).** Even for sofic `Q` it is
  not known that the two-sided action `Q x Q ↷ Q`, or the conjugation action,
  is sofic. GKP derive it only from a positive answer to their Question 4.2,
  which is false in general. The pullback to `F x F` could still be sofic
  without `Q` sofic, as happens for one free factor.
- **Pulling back the Kun--Thom combined action (dies; lane ex3-pfg-negative).**
  The nonsofic `G x G ↷ (G x G)/ΔΓ` of
  [[commuting-sofic-actions-need-not-combine]], pulled back to `F x F'` along
  any homomorphisms, is sofic. `G x 1` acts freely and `G` is residually
  finite, so the kernel `L ∩ (F x 1)` is amenably separable.
  Restriction arguments cannot move the Kazhdan obstruction into `F x F'`
  either, since every subgroup of `F x F'` is Haagerup.
- **Where a counterexample must live (fence, lane ex3-pfg-negative).** By
  [[g-x-free-set-actions-sofic-when-kernel-amenably-separable]] the
  stabilizer needs both `N_1` and `N_2` to fail amenable separability. In
  particular both are infinitely generated and both coordinate actions are
  non-free. For full projections, `Q` is neither residually amenable nor LEF.
  *Sharpened (lane ex3-pfg-positive):* one may take full projections and `Q`
  finitely presented. `Q` must then not be left-right sofic. In particular it
  is not LEA and has no co-amenable left-right sofic subgroup.
