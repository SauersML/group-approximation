---
rg: 2
id: fp-clopen-transitive-full-cantor-group-type-a-proof
kind: route
title: Patch local maps atom by atom for orbits, and transport supported subgroups along a local map onto a clopen set for stabilizers
target: fp-clopen-transitive-full-cantor-groups-have-type-a-actions
requires:
  - type-a-action-gives-boone-higman-for-subgroups
---

Notation as in the target.

**Step 0. Local maps.**
- (a) *Inverses and composites.* If `f` agrees with `d ∈ D` on an open `N`, then
  `f^{-1}` agrees with `d^{-1}` on the open set `f(N)`. If `f, f'` are D-local
  and composable, then near each point `f' f` agrees with `d' d` on
  `N ∩ f^{-1}(N')`. So inverses and composites of D-local maps are D-local.
- (b) *Patching.* If `Y = ⊔_i U_i = ⊔_i U'_i` are finite clopen partitions and
  `f_i : U_i -> U'_i` are D-local, then `⊔_i f_i` is a D-local homeomorphism of
  `Y`, hence in `D` by fullness. The same holds for infinitely many open pieces,
  but only the finite case is used.

**Step 1. Faithful.** Let `g ≠ 1` and `gp ≠ p`. Since `Y` is Hausdorff and
zero-dimensional, there is a clopen `U` with `p ∈ U` and `gp ∉ U`. Then
`U ∈ 𝒮` and `gp ∈ gU \ U`, so `gU ≠ U`.

**Step 2. Finitely many orbits of pairs.** For `(U, W) ∈ 𝒮^2` consider the four
atoms `U ∩ W`, `U \ W`, `W \ U` and `Y \ (U ∪ W)`, and let the *pattern* be the
set of atoms that are nonempty.
- Every homeomorphism preserves the pattern.
- Suppose `(U, W)` and `(U', W')` have the same pattern. For each nonempty atom
  `E` with corresponding atom `E'`, clopen transitivity gives a D-local map
  `E -> E'`. The atoms partition `Y` on both sides. By Step 0(b) the patched map
  is some `g ∈ D`, and `gU = U'`, `gW = W'`.
- There are at most `2^4 = 16` patterns, so at most 16 orbits of ordered pairs.
  Every two-element subset `{U, W}` comes from an ordered pair, so there are at
  most 16 orbits of two-element subsets.

**Step 3. Supported subgroups are copies of `D`.** For nonempty clopen `Z`, let
`D(Z)` be the elements of `D` equal to the identity outside `Z`. Clopen
transitivity gives a D-local map `f : Y -> Z`.
- For `g ∈ D` let `λ(g)` be `f g f^{-1}` on `Z` and the identity on `Y \ Z`. It is
  a homeomorphism of `Y` because `Z` is clopen. On `Z` it is D-local by Step 0(a),
  since `g` agrees with itself everywhere. On `Y \ Z` it agrees with `1`. By
  fullness `λ(g) ∈ D(Z)`.
- For `k ∈ D(Z)`, `k` preserves `Z`, so `μ(k) = f^{-1} k f` is a homeomorphism of
  `Y`. It is D-local by Step 0(a), so `μ(k) ∈ D`.
- `λ` and `μ` are homomorphisms, and they are mutually inverse. So
  `D(Z) ≅ D`.

**Step 4. Stabilizers.** Let `U ∈ 𝒮` and `U^c = Y \ U`, both nonempty. If
`gU = U` then `gU^c = U^c`. Let `g_1` be `g` on `U` and `1` on `U^c`, and `g_2` be
`1` on `U` and `g` on `U^c`. Both are D-local homeomorphisms, hence lie in `D` by
fullness. Then `g = g_1 g_2` with `g_1 ∈ D(U)` and `g_2 ∈ D(U^c)`. Conversely
`D(U)` and `D(U^c)` stabilize `U`, commute, and intersect trivially. So
`Stab_D(U) = D(U) × D(U^c) ≅ D × D` by Step 3. This is finitely generated
because `D` is finitely presented.

**Step 5. Conclusion.** Steps 1, 2 and 4, with hypothesis 3, verify the four
conditions of type (A) quoted verbatim from Zaremsky, arXiv:2405.18354, in
`type-a-action-gives-boone-higman-for-subgroups`. That node's Corollary B,
"Any subgroup of a group admitting an action of type (A) has solvable word
problem and satisfies the Boone--Higman conjecture", gives the stated
consequences. Membership in `B_A` is the definition of the permutational class:
embedding in a group admitting an action of type (A). ∎
