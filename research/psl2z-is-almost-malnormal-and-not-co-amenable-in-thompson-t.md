---
rg: 2
id: psl2z-is-almost-malnormal-and-not-co-amenable-in-thompson-t
kind: claim
title: The piecewise-projective copy of PSL_2(Z) in Thompson's T is almost malnormal, so it, its conjugates and all their subgroups are not co-amenable in T
distinct_from:
  psl2z-in-thompson-t-has-amenable-centralizers-in-v: that bounds centralizers Λ ∩ C(f), the fixed points of conjugation by f; this bounds the intersections Λ ∩ gΛg^{-1}, a different set, by the same breakpoint-permutation device, and draws a co-amenability conclusion.
  thompson-t-orbits-carry-no-invariant-means: that excludes point and finite-set stabilizers as co-amenable subgroups; this excludes the conjugates of PSL_2(Z), which have no finite orbit on the circle.
  thompson-t-co-amenable-subgroup-kills-real-euler-class: that asks for a co-amenable subgroup with vanishing real Euler class and names PSL_2(Z) as its one candidate; this refutes the candidate.
---

**ESTABLISHED.** Let `Φ : PPSL_2(Z) → T` be the isomorphism of `thompson-t-is-isomorphic-to-ppsl2z`
and `Λ = Φ(PSL_2(Z))`. Then:

1. **Almost malnormal.** For every `g ∈ T \ Λ`, the group `Λ ∩ gΛg^{-1}` is finite. Its order
   is at most `|B|!`, where `B` is the (finite, rational, at least two point) breakpoint set of
   `Φ^{-1}(g)`.
2. **Not co-amenable, with a uniform gap.** `ℓ²(T/Λ)` has no almost invariant unit vectors.
   So `T/Λ` carries no `T`-invariant mean.
3. **Inheritance.** No subgroup of any conjugate `tΛt^{-1}` is co-amenable in `T`. This includes
   the free subgroups of finite index in `Λ` and the cyclic subgroups of `Λ`.

The same holds for the image of `PSL_2(Z)` under any isomorphism `PPSL_2(Z) → T`, since
almost malnormality and non-co-amenability are transported by isomorphisms. In particular it
holds for the Minkowski copy `?∘PSL_2(Z)∘?^{-1}`.

**Consequence for the program.** The one concrete candidate `H = PSL_2(Z)` of
`thompson-t-co-amenable-subgroup-kills-real-euler-class` fails, and no witness `H` there can be
contained in a conjugate of `Λ`.

Route: `psl2z-almost-malnormal-not-co-amenable-in-thompson-t-proof`.
