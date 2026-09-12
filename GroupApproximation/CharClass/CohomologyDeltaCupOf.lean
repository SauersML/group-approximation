import GroupApproximation.CharClass.CohomologyDeltaSpecOf
import GroupApproximation.CharClass.CohomologyAssoc
import GroupApproximation.CharClass.CohomologyBridge

/-!
# δ-linearity of the Mayer–Vietoris connecting map over a field

The coefficient-generic form of `CohomologyDeltaCup`:

```text
δ (a ⌣ b|_{U ∩ V}) = δ a ⌣ b,   b ∈ H^q(X; K),
```

after the degree cast `(p+1)+q = (p+q)+1`.  No sign appears: the class `b` sits on the
**right**, so the signed Leibniz rule `d(φ ⌣ ψ) = dφ ⌣ ψ + (−1)^p φ ⌣ dψ` contributes only its
first term once `ψ` is a cocycle, and restriction commutes with the cup product and with the
difference `α_U| − α_V|` of `mvDeltaOf_data`.

## Main results

* `MVDelta.mvDeltaOf_cup` — δ-linearity, with the cast on the right.
* `MVDelta.mvDeltaOf_cup_inclSubtype` — the same in the `inclSubtype` spelling.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.CharClass

noncomputable section

namespace MVDelta

variable {X : TopCat.{0}}

/-! ## 1. Cochain plumbing over `K` -/

theorem cochainPullback_zeroOf {K : Type} [CommRing K] {Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    cochainPullback f n (0 : singularCochainGroup K Y n) = 0 := map_zero _

theorem cochainPullback_subOf {K : Type} [CommRing K] {Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ ψ : singularCochainGroup K Y n) :
    cochainPullback f n (φ - ψ) = cochainPullback f n φ - cochainPullback f n ψ :=
  map_sub _ _ _

/-- Pullback of cochains is contravariantly functorial, over any ring. -/
theorem cochainPullback_compK {K : Type} [CommRing K] {Y Z : TopCat.{0}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (n : ℕ) (φ : singularCochainGroup K Z n) :
    cochainPullback (f ≫ g) n φ = cochainPullback f n (cochainPullback g n φ) := by
  have h : ((singularCochainComplexFunctor K (ModuleCat.of K K)).map (f ≫ g).op).f n
      = (((singularCochainComplexFunctor K (ModuleCat.of K K)).map g.op)
        ≫ ((singularCochainComplexFunctor K (ModuleCat.of K K)).map f.op)).f n := by
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  have h2 := congrArg (fun ψ => ψ.hom φ) h
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h2
  exact h2

/-- Pullback of cochains is a cochain map, over any ring. -/
theorem cochainPullback_coboundaryOf {K : Type} [CommRing K] {Y : TopCat.{0}} (f : X ⟶ Y)
    (n : ℕ) (φ : singularCochainGroup K Y n) :
    cochainPullback f (n + 1) (cochainCoboundary K Y n φ)
      = cochainCoboundary K X n (cochainPullback f n φ) := by
  have hcomm := ((singularCochainComplexFunctor K (ModuleCat.of K K)).map f.op).comm n (n + 1)
  have h := congrArg (fun ψ => ψ.hom φ) hcomm
  simp only [ModuleCat.comp_apply] at h
  exact h.symm

theorem cochainCast_pullbackOf {K : Type} [CommRing K] {Y : TopCat.{0}} (f : Y ⟶ X)
    {m m' : ℕ} (h : m = m') (φ : singularCochainGroup K X m) :
    cochainPullback f m' (cochainCast h φ) = cochainCast h (cochainPullback f m φ) := by
  subst h
  simp only [cochainCast_rfl]

theorem cochainCast_coboundaryOf {K : Type} [CommRing K] {m m' : ℕ} (h : m = m')
    (h' : m + 1 = m' + 1) (φ : singularCochainGroup K X m) :
    cochainCoboundary K X m' (cochainCast h φ)
      = cochainCast h' (cochainCoboundary K X m φ) := by
  subst h
  simp only [cochainCast_rfl]

theorem cochainCup_sub_leftOf {K : Type} [CommRing K] {Z : TopCat.{0}} (p q : ℕ)
    (φ φ' : singularCochainGroup K Z p) (ψ : singularCochainGroup K Z q) :
    cochainCup p q (φ - φ') ψ = cochainCup p q φ ψ - cochainCup p q φ' ψ := by
  rw [eq_sub_iff_add_eq, ← cochainCup_add_left, sub_add_cancel]

/-! ## 2. δ-linearity -/

/-- **δ-linearity of the Mayer–Vietoris connecting map over a field.**  For a global class
`b`, `δ (a ⌣ b|_{U∩V}) = δ a ⌣ b` after the degree cast `(p+1)+q = (p+q)+1`. -/
theorem mvDeltaOf_cup (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) {p q : ℕ}
    (a : Hmod K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p) (b : Hmod K X q) :
    (mvDeltaOf K U V hUV (p + q)).hom
        (cup a (pull (sInclusion ((U : Set X) ∩ (V : Set X))) q b))
      = cohCast (aw_degree_left_succ p q) (cup ((mvDeltaOf K U V hUV p).hom a) b) := by
  obtain ⟨α, hα, aU, aV, γ, hγ, hacls, haUV, hγU, hγV⟩ := mvDeltaOf_data K U V hUV p a
  obtain ⟨β, hβ0, hbcls⟩ := CohClass.clsOfK_surjective (cochainCxK K X) q b
  have hβ : cochainCoboundary K X q β = 0 := hβ0
  have hb : cocycleClassK K X q β hβ = b := hbcls
  -- the restrictions of `β` are cocycles
  have hβU : cochainCoboundary K (TopCat.of (U : Set X)) q
      (cochainPullback (sInclusion (U : Set X)) q β) = 0 := by
    rw [← cochainPullback_coboundaryOf, hβ, cochainPullback_zeroOf]
  have hβV : cochainCoboundary K (TopCat.of (V : Set X)) q
      (cochainPullback (sInclusion (V : Set X)) q β) = 0 := by
    rw [← cochainPullback_coboundaryOf, hβ, cochainPullback_zeroOf]
  have hβW : cochainCoboundary K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) q
      (cochainPullback (sInclusion ((U : Set X) ∩ (V : Set X))) q β) = 0 := by
    rw [← cochainPullback_coboundaryOf, hβ, cochainPullback_zeroOf]
  -- restricting `β|_U` to the intersection is `β|_{U ∩ V}`
  have hrestrU : cochainPullback (subInclusion Set.inter_subset_left) q
        (cochainPullback (sInclusion (U : Set X)) q β)
      = cochainPullback (sInclusion ((U : Set X) ∩ (V : Set X))) q β := by
    rw [← cochainPullback_compK, subInclusion_comp_sInclusion]
  have hrestrV : cochainPullback (subInclusion Set.inter_subset_right) q
        (cochainPullback (sInclusion (V : Set X)) q β)
      = cochainPullback (sInclusion ((U : Set X) ∩ (V : Set X))) q β := by
    rw [← cochainPullback_compK, subInclusion_comp_sInclusion]
  -- the cupped data
  have hα' : cochainCoboundary K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) (p + q)
      (cochainCup p q α
        (cochainPullback (sInclusion ((U : Set X) ∩ (V : Set X))) q β)) = 0 :=
    cochainCup_respects_cocycles p q α _ hα hβW
  have hcup : cochainCoboundary K X (p + 1 + q) (cochainCup (p + 1) q γ β) = 0 :=
    cochainCup_respects_cocycles (p + 1) q γ β hγ hβ
  have hγ' : cochainCoboundary K X (p + q + 1)
      (cochainCast (aw_degree_left_succ p q) (cochainCup (p + 1) q γ β)) = 0 := by
    rw [cochainCast_coboundaryOf (aw_degree_left_succ p q)
      (show p + 1 + q + 1 = p + q + 1 + 1 by omega), hcup, cochainCast_zero]
  have haUV' : cochainPullback (subInclusion Set.inter_subset_left) (p + q)
        (cochainCup p q aU (cochainPullback (sInclusion (U : Set X)) q β))
      - cochainPullback (subInclusion Set.inter_subset_right) (p + q)
        (cochainCup p q aV (cochainPullback (sInclusion (V : Set X)) q β))
      = cochainCup p q α
        (cochainPullback (sInclusion ((U : Set X) ∩ (V : Set X))) q β) := by
    rw [cochainCup_naturality, cochainCup_naturality, hrestrU, hrestrV,
      ← cochainCup_sub_leftOf, haUV]
  have hγU' : cochainPullback (sInclusion (U : Set X)) (p + q + 1)
        (cochainCast (aw_degree_left_succ p q) (cochainCup (p + 1) q γ β))
      = cochainCoboundary K (TopCat.of (U : Set X)) (p + q)
          (cochainCup p q aU (cochainPullback (sInclusion (U : Set X)) q β)) := by
    rw [cochainCast_pullbackOf, cochainCup_naturality, hγU, aw_cochain_leibniz, hβU,
      cochainCup_zero_right, cochainCast_zero, smul_zero, add_zero]
  have hγV' : cochainPullback (sInclusion (V : Set X)) (p + q + 1)
        (cochainCast (aw_degree_left_succ p q) (cochainCup (p + 1) q γ β))
      = cochainCoboundary K (TopCat.of (V : Set X)) (p + q)
          (cochainCup p q aV (cochainPullback (sInclusion (V : Set X)) q β)) := by
    rw [cochainCast_pullbackOf, cochainCup_naturality, hγV, aw_cochain_leibniz, hβV,
      cochainCup_zero_right, cochainCast_zero, smul_zero, add_zero]
  -- the value of `δ` on `a`
  have hdelta : (mvDeltaOf K U V hUV p).hom a = cocycleClassK K X (p + 1) γ hγ := by
    rw [← hacls]
    exact mvDeltaOf_spec K U V hUV p α hα aU aV haUV γ hγ hγU hγV
  -- the left-hand side as the class of a cochain
  have hLHS : cup a (pull (sInclusion ((U : Set X) ∩ (V : Set X))) q b)
      = cocycleClassK K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) (p + q)
          (cochainCup p q α
            (cochainPullback (sInclusion ((U : Set X) ∩ (V : Set X))) q β)) hα' := by
    rw [← hacls, ← hb, pull_mkOf, cup_mkOf]
  rw [hLHS, mvDeltaOf_spec K U V hUV (p + q)
    (cochainCup p q α (cochainPullback (sInclusion ((U : Set X) ∩ (V : Set X))) q β)) hα'
    (cochainCup p q aU (cochainPullback (sInclusion (U : Set X)) q β))
    (cochainCup p q aV (cochainPullback (sInclusion (V : Set X)) q β)) haUV'
    (cochainCast (aw_degree_left_succ p q) (cochainCup (p + 1) q γ β)) hγ' hγU' hγV',
    hdelta, ← hb, cup_mkOf, cohCast_cocycleClassOf K _ _ _ hγ']

/-- The same statement with the subtype inclusion written as `inclSubtype`. -/
theorem mvDeltaOf_cup_inclSubtype (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤)
    {p q : ℕ} (a : Hmod K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p) (b : Hmod K X q) :
    (mvDeltaOf K U V hUV (p + q)).hom
        (cup a (pull (inclSubtype ((U : Set X) ∩ (V : Set X))) q b))
      = cohCast (show p + 1 + q = p + q + 1 by omega)
          (cup ((mvDeltaOf K U V hUV p).hom a) b) :=
  mvDeltaOf_cup K U V hUV a b

end MVDelta

end

end GroupApproximation.CharClass
