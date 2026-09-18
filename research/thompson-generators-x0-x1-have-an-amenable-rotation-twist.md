---
rg: 2
id: thompson-generators-x0-x1-have-an-amenable-rotation-twist
kind: claim
title: "The twist ⟨x_0ρ_{1/2}, x_1⟩ of Thompson's generators by a half rotation is the amenable group Z ≀ Z/3 inside T, so the smallest candidate set {x_0, x_1} is not a witness for non-LAT of T on T/R_D"
distinct_from:
  thompson-t-dyadic-rotation-cosets-are-not-amenably-transitive: that asks for some finite S ⊆ F none of whose rotation twists is amenable; this shows S = {x_0, x_1} is not such a set, unconditionally, so a witness needs at least three elements or other elements.
  liouville-action-criteria-cannot-decide-thompson-f-amenability: that notes that in the regular F-set the set {e, x_0, x_1} forces H = F; this shows that in T/R_D the same three points lie in one orbit of a virtually abelian group, so the dyadic twists really do change the problem.
  finite-subgroups-of-thompson-t-are-cyclic: that classifies the finite subgroups of T; here one generator is a torsion element of order 3 and the group is infinite and virtually Z^3.
---

**ESTABLISHED** through `thompson-generators-x0-x1-have-an-amenable-rotation-twist-proof` (hand proof; also
checked in exact arithmetic by `experiments/rotation-twist-finite-orbits-2026-09-17/amenable_twist_search.py`).

**Notation** as in `jz-question-5-for-thompson-t-implies-f-nonamenable`: `S¹ = R/Z`, `ρ_θ(t) = t + θ`,
`X = T/R_D`, and `x_0, x_1 ∈ F = Stab_T(0)` are the standard generators (left actions,
`x_0 = (0,0)(1/2,1/4)(3/4,1/2)(1,1)`, `x_1` the identity on `[0,1/2]` and a copy of `x_0` on `[1/2,1]`).

**Theorem.** Let `A = x_0ρ_{1/2}` (so `A(t) = x_0(t + 1/2)`) and `B = x_1`. Then:

1. `A` has order 3. It maps `I_0 = [1/2, 1]`, `I_1 = [0, 1/4]`, `I_2 = [1/4, 1/2]` affinely onto
   `I_1`, `I_2`, `I_0` respectively.
2. `N = ⟨B, ABA^{-1}, A²BA^{-2}⟩ ≅ Z³`: the three generators have pairwise disjoint supports
   `(1/2, 1)`, `(0, 1/4)`, `(1/4, 1/2)`.
3. `H = ⟨A, B⟩ = N ⋊ ⟨A⟩ ≅ Z ≀ Z/3`, which is virtually abelian and hence amenable.
4. So `R_D`, `x_0R_D = AR_D` and `x_1R_D = BR_D` lie in one orbit of the amenable subgroup `H ≤ T`. The
   set `S = {x_0, x_1}` is not a witness for `thompson-t-dyadic-rotation-cosets-are-not-amenably-transitive`.

**Census (exact, `classify_twists.py`).** For all `a, b ∈ 2^{-4}Z/Z` (256 pairs), each twist
`⟨x_0ρ_a, x_1ρ_b⟩` falls into one of three classes:
- 242 twists have no finite orbit on `S¹`. They are nonamenable unconditionally, by
  `fg-amenable-subgroups-of-thompson-t-have-finite-orbits`.
- 13 twists contain a copy of `F`, certified by a pair of words with a one-sided orbital
  (`brin-plo-i-one-sided-approach-gives-a-copy-of-f`).
- 1 twist is virtually abelian: `(a, b) = (1/2, 0)`, the group above.

At `2^{-5}` (1024 pairs, `classify_x0x1_K5.json`) the split is 1001 / 22 / 1. Two pairs were left open by the
default word lengths, and both are now closed:
- `(23/32, 1/4)` has no finite orbit once words of length 3 are used (`k5_residual_23-32_1-4.json`).
- `(21/32, 0)` has the finite orbit `{1/16, 15/32}` and contains `F`. The certificate is the pair
  `A^{-1}BA` and `c(A^{-1}BA)c^{-1}` with `c = ABA^{-1}`. Their single orbitals `(3/32, 11/32)` and
  `(11/128, 9/32)` cross, so the first element approaches exactly one end of the common orbital
  `(11/128, 11/32)` (`brin_deep.py explicit`, `brin_explicit_21-32_0.json`).

So at both denominators `(1/2, 0)` is the only twist that escapes unconditionally. The 13 twists that contain
`F` escape only if `F` is amenable. (The census is evidence only; the theorem above does not depend on it.) The escape is invisible to the earlier census in
`thompson-t-dyadic-rotation-cosets-are-not-amenably-transitive` (Attempts, w8), which tested only for commuting
pairs and for finite groups. That entry concluded that "the only possible escape left for `{x_0, x_1}` goes
through point-fixing subgroups, whose amenability is F-level". This theorem corrects it: the escape is a
virtually abelian group with a finite orbit `{0, 1/4, 1/2}` of size 3, and its amenability is unconditional.

**Mechanism (reusable).** If `c ∈ T` has finite order `m` and permutes the arcs of a finite partition, and
`U ⊆ T` is supported inside one arc `I` whose `c`-orbit has `m` distinct arcs, then
`⟨c, U⟩ ≅ ⟨U⟩ ≀ Z/m`. So a set `S ⊆ F` has an amenable twist as soon as one element has a torsion twist of
this kind and the others, twisted or not, generate an amenable group supported in one of its arcs. Any
witness `S` must defeat every such configuration.
