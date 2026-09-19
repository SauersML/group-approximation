import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CohomologyCupProduct

/-!
# `j^*(s^* u) = γ_r(E)`: the relative Euler class restricts to the top Chern class

Item 5 of §1.4 of `notes/LIX_FULL_PROGRAM_2026-09-05.md` asks, besides the existence
of the Thom class `u ∈ H^{2r}(E, E ∖ 0; F₂)` (built in `ThomFreeModule.lean`), for two
compatibilities:

* `z₀^* u = γ_r(E)` for the zero section `z₀ : X → E`;
* for a section `s` of `E` nowhere zero off `Z(s)`, the relative Euler class
  `s^* u ∈ H^{2r}(X, X ∖ Z(s))` satisfies `j^*(s^* u) = γ_r(E)`.

Both are the *same* two-line diagram chase, and this file does it once.  Write
`π : E → X` for the projection and `σ` for either `z₀` or `s`; then `π ∘ σ = id_X`, so
on cohomology `σ^* ∘ π^* = id`.  Since the absolute class `j_E^*(u) ∈ H^{2r}(E)` is
`π^*(γ_r(E))` (which for `z₀` is the *definition* of the Euler class, and in general
follows because `π^*` is an isomorphism, `E` deformation-retracting to the zero
section), naturality of `j^*` for the map of pairs `σ : (X, X ∖ Z(σ)) → (E, E ∖ 0)`
gives

```text
j^*(σ^* u) = σ^*(j_E^* u) = σ^*(π^* γ_r(E)) = γ_r(E).
```

The statement is over `ModuleCat.{0} (ZMod 2)`, where the vendored singular cohomology
lives, and the hypotheses are the three squares that `cc-relative` (naturality of `j^*`
for maps of pairs, need (B5)), `cc-bundle` (the zero section and the projection,
(C1)/(C2)) and `cc-projective` ((D1)) owe.

Both a categorical form (commuting triangles/squares of `ModuleCat` morphisms) and a
pointwise form are provided, since peers may deliver either.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

section Bridge

variable {R : Type*} [Ring R]

/-- Applying a composite of `ModuleCat` morphisms to an element. -/
theorem hom_apply_comp {A B C : ModuleCat.{0} R} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g).hom x = g.hom (f.hom x) := rfl

/-- Pointwise form of a commuting triangle. -/
theorem hom_apply_of_comp_eq {A B C : ModuleCat.{0} R} {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ C}
    (hfg : f ≫ g = h) (x : A) : g.hom (f.hom x) = h.hom x := by
  rw [← hfg, hom_apply_comp]

/-- Pointwise form of "this composite is the identity". -/
theorem hom_apply_of_comp_eq_id {A B : ModuleCat.{0} R} {f : A ⟶ B} {g : B ⟶ A}
    (hfg : f ≫ g = 𝟙 A) (x : A) : g.hom (f.hom x) = x := by
  rw [hom_apply_of_comp_eq hfg x]
  rfl

end Bridge

section Naturality

variable {HrelE HE HX HrelX : ModuleCat.{0} (ZMod 2)}

/-- **`j^*(σ^* u) = γ_r`, pointwise hypotheses.**

* `HrelE = H^{2r}(E, E ∖ 0)`, `HE = H^{2r}(E)`, `HX = H^{2r}(X)`,
  `HrelX = H^{2r}(X, X ∖ Z(σ))`;
* `jE`, `jX` are the two maps `j^*` forgetting the relative structure;
* `sRel`, `sAbs` are the pullbacks along `σ` of pairs and of spaces;
* `piStar` is the pullback along the bundle projection `π`.

`hnat` is naturality of `j^*` for the map of pairs `σ`, `hsection` is `π ∘ σ = id`, and
`hu` says the absolute Thom class is `π^*` of the top Chern class. -/
theorem topClass_eq_of_naturality (jX : HrelX ⟶ HX)
    (sRel : HrelE ⟶ HrelX) (sAbs : HE ⟶ HX) (piStar : HX ⟶ HE)
    {jEu : HE} {u : HrelE} {gammaR : HX}
    (hnat : jX.hom (sRel.hom u) = sAbs.hom jEu)
    (hu : jEu = piStar.hom gammaR)
    (hsection : sAbs.hom (piStar.hom gammaR) = gammaR) :
    jX.hom (sRel.hom u) = gammaR := by
  rw [hnat, hu, hsection]

/-- **`j^*(σ^* u) = γ_r`, categorical hypotheses.**  Same statement with the two
compatibilities given as commuting diagrams of `ModuleCat` morphisms:
`σ^*_{pair} ≫ j^*_X = j^*_E ≫ σ^*` and `π^* ≫ σ^* = 𝟙`. -/
theorem topClass_eq_of_naturality' (jE : HrelE ⟶ HE) (jX : HrelX ⟶ HX)
    (sRel : HrelE ⟶ HrelX) (sAbs : HE ⟶ HX) (piStar : HX ⟶ HE)
    (hnat : sRel ≫ jX = jE ≫ sAbs) (hsection : piStar ≫ sAbs = 𝟙 HX)
    {u : HrelE} {gammaR : HX} (hu : jE.hom u = piStar.hom gammaR) :
    jX.hom (sRel.hom u) = gammaR := by
  refine topClass_eq_of_naturality jX sRel sAbs piStar (jEu := jE.hom u) ?_ hu ?_
  · rw [← hom_apply_comp sRel jX u, hnat, hom_apply_comp]
  · rw [← hu, ← hom_apply_comp jE sAbs u]
    rw [hom_apply_comp jE sAbs u, hu]
    exact hom_apply_of_comp_eq_id hsection gammaR

end Naturality

end GroupApproximation.CharClass
