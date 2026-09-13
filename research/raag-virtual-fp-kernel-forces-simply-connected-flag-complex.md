---
rg: 2
id: raag-virtual-fp-kernel-forces-simply-connected-flag-complex
kind: claim
title: If a finite-index subgroup of a right-angled Artin group maps onto Z with finitely presented kernel, the flag complex is simply connected
distinct_from:
  raag-virtual-fp-n-kernel-forces-acyclic-flag-complex: that concludes vanishing homology of L from a kernel of type FP_n and is proved; this concludes that the fundamental group of L is trivial from a finitely presented kernel, the remaining case of Zaremsky's Problem 1.19.
---

For every finite flag complex `L` and finite-index subgroup `H ≤ A_L`: if some epimorphism
`H → Z` has finitely presented kernel, then `π_1(L) = 1`.

Why it matters. With `raag-virtual-fp-n-kernel-forces-acyclic-flag-complex` it gives the
conjecture of Zaremsky's Problem 1.19 for every `n` (route
`raag-virtual-fn-kernel-conjecture-via-simple-connectivity`). Conversely it follows from the
case `n = 2` of the conjecture, given that a finitely presented kernel on `A_L` itself forces
`L` to be simply connected (the remark printed under Problem 1.23, from the Σ-invariants of
Meier--Meinert--VanWyk). The homological theorem already gives `H_1(L; Z) = 0`, so a
counterexample needs a nontrivial perfect `π_1(L)`.

## Attempts

- 2026-09-13, lane z1-19-raag-kernel, Bestvina--Brady Morse theory on finite covers. Let `f` be
  an `H`-equivariant height on the CAT(0) cube complex `X̃` that is affine on cubes and has
  nonzero weight on every hyperplane of `X̂ = X̃/H`. The vertex link of `X̃` is the
  octahedralization `OL` (vertices `v^±`), and the ascending link `A` and descending link `D` at a
  vertex are full subcomplexes of `OL`. A vertex `v` can have both `v^+` and `v^−` ascending (a
  local minimum along the `v`-line). Forgetting signs is simplicial and retracts `A` onto the
  full subcomplex `L_{V_A}` of `L` on the vertices touched by `A` (choose one ascending sign per
  vertex), and likewise `D` onto `L_{V_D}`, with `V_A ∪ V_D = V(L)`. So simply connected ascending
  and descending links force `L_{V_A}` and `L_{V_D}` to be simply connected; when `π_1(L) ≠ 1`
  both must be proper, and some vertex must be a local minimum and another a local maximum.
  This is not an obstruction (the Morse lemma is only sufficient, and the conditions can hold
  with both proper), but it pins down what a counterexample built this way must look like.
- 2026-09-13, commensurability. `A_L` has finite index in a right-angled Coxeter group
  `W_{L'}` (Davis--Januszkiewicz), and virtual kernels onto `Z` with finitely presented kernel
  pass between commensurable groups (intersect with the common finite-index subgroup). So the
  claim for `L` is equivalent to: no finite-index subgroup of `W_{L'}` maps onto `Z` with a
  finitely presented kernel. Jankiewicz--Norin--Wise height functions with states on covers of
  the Davis complex have ascending links that are full subcomplexes of `L'`, a larger family
  than full subcomplexes of `OL`. This is the most promising search space for a counterexample.
- Open idea: find a character-independent invariant that sees `π_1(L)` the way skew-field Betti
  numbers see `H_*(L)`. Division-ring coefficients see only homology.
