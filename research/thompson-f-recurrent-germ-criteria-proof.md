---
rg: 2
id: thompson-f-recurrent-germ-criteria-proof
kind: route
title: Recurrent singular orbits make F′ act trivially on V; simplicity of F′ makes each germ map injective or trivial; trivial everywhere puts F′ into [[H]]
target: thompson-f-recurrent-germ-criteria-return-f-as-an-input
requires:
  - jndls-recurrent-groupoid-extension-theorem
  - recurrent-orbits-force-every-z3-to-meet-the-stabilizer
  - thompson-f-recurrent-f-sets-factor-through-the-abelianization
  - thompson-f-rigid-interval-subgroups-facts
---

Notation is as in the claim. Fix an isomorphism `θ : F → F_0`, so `F_0′ = θ(F′)`.

**Step 0 (every orbit in `V` is recurrent).** Let `v ∈ V`. By the definition of `V`, `v = g·s` for
some `g ∈ G` and some singular `s`. So `G·v = G·s`, and the Schreier graphs `Γ(v,G)` and `Γ(s,G)`
coincide. By condition (3), `Γ(v,G)` is recurrent.

**Step 1 (`F_0′` fixes `V` pointwise).** Let `v ∈ V`.
- By item 1 (heredity) of `recurrent-orbits-force-every-z3-to-meet-the-stabilizer`, the finitely
  generated subgroup `F_0` acts recurrently on `F_0·v`.
- Pull back by `θ`. Then `F_0·v` is the transitive `F`-set `F/K` with `K = θ^{-1}(Stab_{F_0}(v))`, and
  its Schreier graph is recurrent. The same item says recurrence does not depend on the finite
  generating set.
- By `thompson-f-recurrent-f-sets-factor-through-the-abelianization`, `K ⊇ F′`. So `F_0′ = θ(F′)`
  fixes `v`.

**Step 2 (dichotomy at one point).** Let `v ∈ V`. By Step 1 every `k ∈ F_0′` fixes `v`, so `(k,v)` is a
germ with origin and target `v`. It lies in the germ group `𝒢_v` of `jndls-recurrent-groupoid-extension-theorem`.
- The composition rule `(k_1,v)(k_2,v) = (k_1k_2,v)` makes `γ_v : F_0′ → 𝒢_v`, `k ↦ (k,v)`, a
  homomorphism.
- Its kernel `N_v` is normal in `F_0′ ≅ F′`, and `F′` is simple by (F1) of
  `thompson-f-rigid-interval-subgroups-facts`.
- So either `N_v = 1`, and `γ_v` is injective, or `N_v = F_0′`, and every `k ∈ F_0′` agrees with the
  identity on a neighbourhood of `v`.

**Step 3 (`F′` contains a copy of `F`).** By (F1), `F′` is the set of elements supported in `(0,1)`. So
`F[1/4,3/4] ≤ F′`, and `F[1/4,3/4] ≅ F` by (F2). Hence `F_0′ ⊇ θ(F[1/4,3/4]) ≅ F`, and every
group containing an injective image of `F_0′` contains a copy of `F`.

**Step 4, case (A).** Suppose `N_v = 1` for some `v ∈ V`. Then `𝒢_v ⊇ γ_v(F_0′) ≅ F′`, which
contains a copy of `F` by Step 3. The germ groups along the orbit `G·v` are conjugate in the groupoid,
by `(g,v) 𝒢_v (g,v)^{-1} = 𝒢_{g v}`. This orbit contains a singular point, by Step 0. So the
conclusion holds on either reading of condition (4).

**Step 5, case (B).** Suppose `N_v = F_0′` for every `v ∈ V`. Let `k ∈ F_0′` and `x ∈ X`.
- *If `x` is singular,* then `x ∈ V`. So `k` is the identity near `x`, and `(k,x) = (1,x)`. The
  identity homeomorphism lies in the group `[[H]]`, so `(1,x) ∈ H`.
- *If `x` is not singular,* then `(g,x) ∈ H` for every `g ∈ G`, by the definition of singular. In
  particular `(k,x) ∈ H`.
- So every germ of `k` lies in `H`, and `k ∈ [[H]]` by the definition of the topological full
  group. Hence `F_0′ ≤ G ∩ [[H]]`, and `[[H]]` contains a copy of `F` by Step 3.

**Exclusivity.** In case (A) the nontrivial group `F_0′` has an element that is not the identity near
`v`, so (B) fails. If (A) fails, then every `N_v = F_0′` by Step 2, which is (B).

**Corollaries.**
- *Corollary 1.* Amenability passes to subgroups. So in case (A), input (4) of JNdlS Theorem 3.1
  implies amenability of `F`, and in case (B) input (1) does.
- *Corollary 2.* This is the contrapositive of Steps 0–5. If every singular orbit were recurrent,
  then Steps 1–5 would apply and put `F` into `G ∩ [[H]]` or into some `𝒢_v`.

Condition (2) of Theorem 3.1 is never used. ∎
