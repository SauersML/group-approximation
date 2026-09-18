---
rg: 2
id: rel-hyperbolic-fp-simple-peripherals-proof
kind: route
title: Amalgamate each peripheral subgroup with its overgroup, one at a time, using Dahmani's combination theorem
target: rel-hyperbolic-groups-embed-with-fp-simple-peripherals
requires:
  - relatively-hyperbolic-dehn-filling
---

(`relatively-hyperbolic-dehn-filling` is listed only as the repo's anchor for the
definitions of relative hyperbolicity in use; its content is not used.)

**Input, read at source.** F. Dahmani, *Combination of convergence groups*, Geom.
Topol. 7 (2003) 933--963, arXiv:math/0203258, Theorem 0.1(2), paraphrased: if `G`
is hyperbolic relative to a family `𝒢`, `P ∈ 𝒢`, and `A` is a finitely generated
group containing a copy of `P`, then `A *_P G` is hyperbolic relative to the
conjugates of the images of the members of `𝒢` not conjugate to `P` in `G`,
together with the conjugates of `A`. Dahmani works with Bowditch's definition
(geometrically finite convergence actions with finitely generated maximal
parabolic subgroups).

**Item 1.** Put `Γ_0 = G` with family `𝒢_0` = the conjugates of `P_1, ..., P_m`.
Given `Γ_{i-1}` hyperbolic relative to `𝒢_{i-1}` = the conjugates of
`S_1, ..., S_{i-1}` and of the images of `P_i, ..., P_m`, apply Theorem 0.1(2)
with `P = P_i ∈ 𝒢_{i-1}` and `A = S_i`. Then `Γ_i = S_i *_{P_i} Γ_{i-1}` is
hyperbolic relative to `𝒢_i` = the conjugates of `S_1, ..., S_i` and of the images
of `P_{i+1}, ..., P_m`. The members of `𝒢_{i-1}` not conjugate to `P_i` are exactly
these, because distinct members of the chosen list are non-conjugate maximal
parabolic subgroups. After `m` steps, `Ĝ = Γ_m` is hyperbolic relative to the
conjugates of `S_1, ..., S_m`. Each factor embeds in an amalgamated free product
(normal form theorem, standard, not re-read), so `G ≤ Γ_1 ≤ ... ≤ Ĝ`.

**Item 2.** Suppose `G = (F(X) * P_1 * ... * P_m) / <<R>>` with `X` and `R` finite,
and each `P_i -> G` injective (Osin's finite relative presentation). Let
`Q = (F(X) * S_1 * ... * S_m) / <<R>>`, reading `R` through `P_i -> S_i`. A
homomorphism `Q -> H` is the same as homomorphisms `F(X) -> H` and `S_i -> H`
whose combination kills `R`. A homomorphism `Ĝ -> H` is the same as a homomorphism
`G -> H` and homomorphisms `S_i -> H` that agree on each `P_i`, which again is the
same data. So `Q ≅ Ĝ` as colimits of the same diagram. If each `S_i` is finitely
presented, then `Q` has a finite presentation: `X`, the generators of the `S_i`,
the relators of the `S_i`, and `R`.

Trust note for item 2: for a finitely generated group with finitely generated
peripheral subgroups, Bowditch's and Osin's definitions agree, so a finite relative
presentation exists. This equivalence is standard (Osin, Mem. AMS 179 (2006);
Hruska, AGT 10 (2010)) but was not re-read here. Item 1 does not depend on it.

**Item 3.** Trust note: a group hyperbolic relative to subgroups with solvable
word problem has solvable word problem (Farb, GAFA 8 (1998); Osin, Mem. AMS 179
(2006)). Cited, not read at source. Item 1 and the Corollary's embedding do not
depend on it.

**Corollary.** Take `S_i` finitely presented simple containing `P_i`. Then
`G ≤ Ĝ` with `Ĝ` hyperbolic relative to `{S_i}` by item 1.
