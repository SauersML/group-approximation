---
rg: 2
id: thompson-f-not-in-recurrent-wobbling-groups-proof
kind: route
title: Each F-orbit roughly embeds in the recurrent graph by geodesics, so it is recurrent and F′ fixes every vertex
target: thompson-f-does-not-embed-in-wobbling-groups-of-recurrent-graphs
requires:
  - thompson-f-recurrent-f-sets-factor-through-the-abelianization
  - lyons-peres-energy-rough-embedding-and-polya-transience
---

Item 2 includes item 1, since `F′ ⊆ F` is what is concluded and a homomorphism to `W(Γ)` is an action
by bounded displacement. So it suffices to treat `F` itself acting on `V` with bounded displacement.

**Setup.** Let `S = (s_1, …, s_m)` be a finite symmetric generating multiset of `F`, and
`R = max_i sup_v d_Γ(v, s_i v)`. Fix `v ∈ V`, and let `N = Sch(F·v, S)` be the orbit network of
`recurrent-orbits-force-every-z3-to-meet-the-stabilizer`.

**Rough embedding `N → Γ`.**
- Let `φ` be the inclusion `F·v ⊆ V`.
- For each edge `⟨x, x′⟩` of `N` (so `x ≠ x′ = s_i x` for some `i`), choose a geodesic `Φ(⟨x,x′⟩)` of
  `Γ` from `x` to `x′`, and use its reverse for `⟨x′,x⟩`. It is nonempty and simple, and has length
  at most `R`.
- The resistance of `⟨x,x′⟩` in `N` is `1/c(x,x′) ≥ 1/m`, so (i) holds with `α = R m`.
- An edge `e′` of `Γ` lies on `Φ(⟨x,x′⟩)` only if `x` is within distance `R` of an endpoint of `e′`.
  There are at most `2 (D+1)^R` such `x`, and each has at most `m` neighbours `x′` in `N`. So (ii)
  holds with `β = 4 m (D+1)^R`, counting both orientations.

**Conclusion.**
- By Theorem 2.17 of `lyons-peres-energy-rough-embedding-and-polya-transience`, if `N` were transient
  then `Γ` would be transient. So `N` is recurrent.
- The `F`-set `F·v ≅ F/Stab_F(v)` is recurrent, so `Stab_F(v) ⊇ F′` by
  `thompson-f-recurrent-f-sets-factor-through-the-abelianization`.
- As `v` was arbitrary, `F′` fixes every vertex.
- `F′ ≠ 1`, so the action is not faithful. Applied to `F ⊆ G` acting through `ρ`, this gives
  `ρ(F′) = 1`. ∎
