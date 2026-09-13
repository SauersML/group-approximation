---
rg: 2
id: orbit-finite-affine-actions-are-type-a
kind: claim
title: A semidirect product S ⋊ W acting affinely on S is of type (A) exactly when it is finitely presented, W is finitely generated and W has finitely many orbits on S
distinct_from:
  fiber-product-conjugation-action-lemma: that computes the two-sided translation action of a fiber product T x_Q T on a normal subgroup N, whose stabilizer is the diagonal and whose pair orbits are T-conjugacy classes; this is the affine action of S ⋊ W for an arbitrary group W of automorphisms, whose pair orbits are the W-orbits on S. The N = T case of that lemma with Z(T) = 1 is the special case W = Inn(S) here.
  normalizer-image-of-type-a-actor-is-type-a: that enlarges an existing type (A) actor by normalizing permutations; this produces a type (A) actor from a group of automorphisms that need not act oligomorphically on anything, only with finitely many orbits on the points of S.
  fp-full-binary-cantor-groups-have-type-a-actions: that is the clopen action of a full Cantor group containing V; this is the affine action of a semidirect product on its normal factor, which needs no Cantor space.
  permutational-boone-higman-conjecture: that is the open universality statement; this is an elementary criterion recognizing one family of type (A) actors, and it does not by itself embed any input.
---

**ESTABLISHED** by `orbit-finite-affine-type-a-proof`. Elementary; no novelty
is claimed (the Mikhailova case `W = Inn(S)` is already on main as
`fiber-product-conjugation-action-lemma`).

## Statement

Let `S` be a group, `W <= Aut(S)` a group of automorphisms, and
`Γ = S ⋊ W` with multiplication `(s,w)(s',w') = (s·w(s'), ww')`. Let `Γ` act
on the set `S` by

    (s, w) · x  =  s · w(x).

1. **Action.** This is an action. It is faithful and transitive,
   `Stab_Γ(1) = {(1,w) : w ∈ W} ≅ W`, and `Stab_Γ(x) = (x,1) Stab_Γ(1) (x,1)^(-1)`.
2. **Pair orbits.** `(x, y) ↦ W·(x^(-1) y)` induces a bijection from the
   `Γ`-orbits on `S × S` to the `W`-orbits on `S`.
3. **Criterion.** The action is of type (A) in the sense of BFFHZ and Zaremsky
   (`type-a-action-gives-boone-higman-for-subgroups`) if and only if
   - `Γ` is finitely presented,
   - `W` is finitely generated, and
   - `W` has finitely many orbits on `S`.
4. **Necessary conditions.** If the action is of type (A) then:
   - (a) `W` is finitely presented, being a retract of `Γ`;
   - (b) `S` is countable;
   - (c) `S` realizes only finitely many element orders (orders in `N ∪ {∞}`
     are `Aut(S)`-invariant);
   - (d) if `S` is infinite, `W` is infinite.
5. **Payoff.** If the three conditions of item 3 hold, every subgroup of
   `S ⋊ W`, in particular every subgroup of `W`, has solvable word problem and
   embeds in a finitely presented simple group.

## Definition used

BFFHZ, arXiv:2503.21882, lines 120–125 of the text extracted on MSI
(`/scratch.global/sauer354/bh-reviewer/2503.21882.txt`), verbatim:

> "Given a group Γ acting faithfully on a set S, we say that the action is of
> type (A) if: (i) The group Γ is ﬁnitely presented. (ii) The stabilizer
> Stab_Γ(s) is ﬁnitely generated for all s ∈ S. (iii) The action has ﬁnitely
> many orbits of pairs, i.e., the diagonal action of Γ on S × S has ﬁnitely
> many orbits."

Zaremsky's form (quoted verbatim on `type-a-action-gives-boone-higman-for-subgroups`)
counts orbits of two-element subsets instead. The two counts are finite together:
each orbit of two-element subsets is the image of at most two orbits of ordered
pairs, and the diagonal of `S × S` is one further orbit when the action is
transitive.

## Where this sits

- **Mikhailova case.** If `Z(S) = 1` and `W = Inn(S)`, then `S ⋊ Inn(S) ≅ S × S`
  acting by `(a,b)·x = a x b^(-1)`, and item 2 says pair orbits are conjugacy
  classes. So `every-wp-group-embeds-in-fp-conjugacy-finite-group` already yields
  permutational Boone–Higman, not only Boone–Higman, and at `G = Z` it would answer
  Makowsky's problem FP19 positively (an infinite finitely presented group with
  finitely many conjugacy classes).
- **The input must enter through `W`.** `S` is normal with finitely many element
  orders, so the hard part of a universal construction is a finitely presented `W`
  containing the input and acting with finitely many orbits on some countable group
  `S`, with `S ⋊ W` finitely presented. That target is recorded as
  `decidable-groups-embed-in-orbit-finite-affine-actors`.
