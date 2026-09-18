---
rg: 2
id: cocompact-fuchsian-groups-v-all-or-none-proof
kind: route
title: Proof that V's subgroups are closed under commensurability, and that the cocompact Fuchsian groups form one commensurability class
target: cocompact-fuchsian-groups-embed-in-v-all-or-none
requires: []
---

Lane proof, elementary.

**Wreath products in V.** Let `K ≤ V` and `n >= 1`. Take a complete prefix code
`c_1, ..., c_n` of the binary tree, so the Cantor set `C` is the disjoint union of
the cones `c_i C`; such codes exist for every `n >= 1`. Let `K_i` be the conjugate
of `K` by the prefix map `w ↦ c_i w`, acting on `c_i C` and as the identity
elsewhere. It lies in `V`, since elements of `V` restricted to a cone and conjugated
by a prefix map are again prefix replacements. The `K_i` have disjoint supports, so
they generate `K^n`. For `σ ∈ S_n`, the prefix swap `c_i w ↦ c_{σ(i)} w` lies in `V`
and conjugates `K_i` onto `K_{σ(i)}` compatibly with the identifications. So these
generate the permutational wreath product `K ≀ S_n ≤ V`.

**Part 1.** Let `H ≤ G` have index `n`, with `H ≤ V`. By the Kaloujnine--Krasner
embedding (the induced monomial representation), `G ↪ H ≀ S_n ≤ V`. If `G` and
`G'` share a finite-index subgroup `K`, and `G ≤ V`, then `K ≤ V`, and so `G' ≤ V`.

**Part 2.** A cocompact Fuchsian group has a torsion-free finite-index subgroup
(Selberg's lemma), which is `π_1(Σ_g)` for some `g >= 2`. A closed non-orientable
hyperbolic surface has an orientable double cover of genus `>= 2`. For `g >= 2`, the
closed surface `Σ_g` is a degree `g-1` cover of `Σ_2`, since Euler characteristic
multiplies by the degree: `2 - 2g = (g-1)(2 - 2·2)`. So `π_1(Σ_g)` has index `g-1` in
`π_1(Σ_2)`, and every group listed shares a finite-index subgroup with `π_1(Σ_2)`. ∎
