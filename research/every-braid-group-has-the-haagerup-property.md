---
rg: 2
id: every-braid-group-has-the-haagerup-property
kind: claim
title: Every braid group B_n has the Haagerup property
distinct_from:
  some-braid-group-lacks-the-haagerup-property: that claim is the negation of this one; exactly one of the two holds
---

For every `n ≥ 1`, Artin's braid group `B_n` admits a proper conditionally
negative definite function (equivalently, a proper affine isometric action on a
Hilbert space).

This is the affirmative answer to Zaremsky Problem 3.7
(`zaremsky-3-07-braid-groups-haagerup`). Since `B_n ≤ B_{n+1}`, it is
equivalent to the property for infinitely many `n`. It holds for `n ≤ 3`.

## Attempts

- **Proper actions on CAT(0) cube complexes** (possibly infinite-dimensional)
  would suffice, through hyperplane-counting cocycles. No such action is known
  for `B_n` with `n ≥ 4`. The CAT(0) structures found for small `n` (reported:
  Brady–McCammond for `n ≤ 5`, Haettel–Kielak–Schwer for `n = 6`; see the 3.06
  region, lane z3-06-braid-cat0) are piecewise Euclidean and not cubical. A proper
  cocompact CAT(0) action alone does not give the Haagerup property.
- **Finite products of quasi-trees.** Bestvina–Bromberg–Fujiwara give proper
  actions of mapping class groups on finite products of quasi-trees. Quasi-trees
  are not median, so this yields no conditionally negative definite function. The
  missing input is a proper action on a finite product of genuine trees, median
  spaces or measured wall spaces.
- **Induction through the Artin combing `P_n = F_{n−1} ⋊ P_{n−1}`.** The property
  does not pass to extensions with free kernel and non-amenable quotient in
  general (compare `Z^2 ⋊ SL_2(Z)` with abelian kernel). A proof needs a proper
  cocycle on `F_{n−1}` that is controlled under the pure braid automorphisms.
  These include pseudo-Anosov monodromies that distort word length
  exponentially, so no invariant proper function on the fiber exists and the
  Cornulier–Stalder–Valette invariant-structure criterion for semidirect products
  does not apply as stated.
- **Forgetful maps.** `P_n → ∏_{i=1}^n P_{n−1}` (forget strand `i`) has kernel the
  Brunnian braid group, which is free (a subgroup of the free kernel of one
  forgetful map). The property for `P_{n−1}` gives it for the image; the
  extension by the free Brunnian kernel is again the gap.
- **Smallest case.** `B_4` is undecided; see the `B_4` claims of this region as
  they land.
