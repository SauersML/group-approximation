import GroupApproximation.CharClass.CohomologyDeltaValue
import GroupApproximation.CharClass.CohomologyAssoc

/-!
# δ-linearity of the Mayer–Vietoris connecting map

The connecting map of the Mayer–Vietoris sequence is linear over the cohomology
ring of the ambient space:

```text
δ (a ⌣ b|_{U ∩ V}) = δ a ⌣ b,   b ∈ H^q(X),
```

after the degree cast `(p+1)+q = (p+q)+1`.  This is what makes Leray–Hirsch, the
Gysin sequence and the ring structure of projective space available, and it is
the last chain-level input the topology side of the LIX program needs.

The proof is entirely at the level of cochains.  `mvDelta_data` produces, for the
class `a`, a cocycle `α` on `U ∩ V`, cochains `aU`, `aV` restricting to it, and a
global cocycle `γ` with `γ|_U = δ aU` and `γ|_V = δ aV`.  Cupping every one of
those with a cocycle `β` representing `b` gives data for `a ⌣ b|_{U∩V}` whose
ambient cocycle is `γ ⌣ β`: the Leibniz rule contributes only the left term
because `β` is a cocycle, and the cup product commutes with restriction.  So
`mvDelta_spec` computes both sides to the same class.

## Main results

* `MVDelta.mvDelta_cup` — δ-linearity, with the cast on the right.
* `MVDelta.mvDelta_cup_inclSubtype` — the same in the `inclSubtype` spelling.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.CharClass

noncomputable section

namespace MVDelta

variable {X : TopCat.{0}}

/-! ## 1. Cochain plumbing -/

theorem cochainPullback_zero {Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    cochainPullback f n (0 : singularCochainGroup (ZMod 2) Y n) = 0 := map_zero _

/-- Pullback of cochains is contravariantly functorial. -/
theorem cochainPullback_comp' {Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Z n) :
    cochainPullback (f ≫ g) n φ = cochainPullback f n (cochainPullback g n φ) := by
  have h : ((singularCochainComplexFunctor (ZMod 2)
        (ModuleCat.of (ZMod 2) (ZMod 2))).map (f ≫ g).op).f n
      = (((singularCochainComplexFunctor (ZMod 2)
          (ModuleCat.of (ZMod 2) (ZMod 2))).map g.op)
        ≫ ((singularCochainComplexFunctor (ZMod 2)
          (ModuleCat.of (ZMod 2) (ZMod 2))).map f.op)).f n := by
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  have h2 := congrArg (fun ψ => ψ.hom φ) h
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h2
  exact h2

/-- Pullback of cochains is a cochain map. -/
theorem cochainPullback_coboundary' {Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y n) :
    cochainPullback f (n + 1) (cochainCoboundary (ZMod 2) Y n φ)
      = cochainCoboundary (ZMod 2) X n (cochainPullback f n φ) := by
  have hcomm := ((singularCochainComplexFunctor (ZMod 2)
      (ModuleCat.of (ZMod 2) (ZMod 2))).map f.op).comm n (n + 1)
  have h := congrArg (fun ψ => ψ.hom φ) hcomm
  simp only [ModuleCat.comp_apply] at h
  exact h.symm

/-- The degree cast commutes with pullback. -/
theorem cochainCast_pullback {Y : TopCat.{0}} (f : Y ⟶ X) {m m' : ℕ} (h : m = m')
    (φ : singularCochainGroup (ZMod 2) X m) :
    cochainPullback f m' (cochainCast h φ) = cochainCast h (cochainPullback f m φ) := by
  subst h
  simp only [cochainCast_rfl]

/-- The degree cast commutes with the coboundary. -/
theorem cochainCast_coboundary {m m' : ℕ} (h : m = m') (h' : m + 1 = m' + 1)
    (φ : singularCochainGroup (ZMod 2) X m) :
    cochainCoboundary (ZMod 2) X m' (cochainCast h φ)
      = cochainCast h' (cochainCoboundary (ZMod 2) X m φ) := by
  subst h
  simp only [cochainCast_rfl]

/-! ## 2. δ-linearity -/

/-- **δ-linearity of the Mayer–Vietoris connecting map.**  For a global class `b`,
`δ (a ⌣ b|_{U∩V}) = δ a ⌣ b` after the degree cast `(p+1)+q = (p+q)+1`. -/
theorem mvDelta_cup (U V : Opens X) (hUV : U ⊔ V = ⊤) {p q : ℕ}
    (a : Hmod2 (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p) (b : Hmod2 X q) :
    (mvDelta U V hUV (p + q)).hom
        (cup a (pull (sInclusion ((U : Set X) ∩ (V : Set X))) q b))
      = cohCast (aw_degree_left_succ p q) (cup ((mvDelta U V hUV p).hom a) b) := by
  obtain ⟨α, hα, aU, aV, γ, hγ, hacls, haUV, hγU, hγV⟩ := mvDelta_data U V hUV p a
  obtain ⟨β, hβ0, hbcls⟩ := CohClass.clsOf_surjective (cochainCxZMod2 X) q b
  have hβ : cochainCoboundary (ZMod 2) X q β = 0 := hβ0
  have hb : cocycleClass X q β hβ = b := hbcls
  -- the restrictions of `β` are cocycles
  have hβU : cochainCoboundary (ZMod 2) (TopCat.of (U : Set X)) q
      (cochainPullback (sInclusion (U : Set X)) q β) = 0 := by
    rw [← cochainPullback_coboundary', hβ, cochainPullback_zero]
  have hβV : cochainCoboundary (ZMod 2) (TopCat.of (V : Set X)) q
      (cochainPullback (sInclusion (V : Set X)) q β) = 0 := by
    rw [← cochainPullback_coboundary', hβ, cochainPullback_zero]
  have hβW : cochainCoboundary (ZMod 2) (TopCat.of ↥((U : Set X) ∩ (V : Set X))) q
      (cochainPullback (sInclusion ((U : Set X) ∩ (V : Set X))) q β) = 0 := by
    rw [← cochainPullback_coboundary', hβ, cochainPullback_zero]
  -- restricting `β|_U` to the intersection is `β|_{U ∩ V}`
  have hrestrU : cochainPullback (subInclusion Set.inter_subset_left) q
        (cochainPullback (sInclusion (U : Set X)) q β)
      = cochainPullback (sInclusion ((U : Set X) ∩ (V : Set X))) q β := by
    rw [← cochainPullback_comp', subInclusion_comp_sInclusion]
  have hrestrV : cochainPullback (subInclusion Set.inter_subset_right) q
        (cochainPullback (sInclusion (V : Set X)) q β)
      = cochainPullback (sInclusion ((U : Set X) ∩ (V : Set X))) q β := by
    rw [← cochainPullback_comp', subInclusion_comp_sInclusion]
  -- the cupped data
  have hα' : cochainCoboundary (ZMod 2) (TopCat.of ↥((U : Set X) ∩ (V : Set X))) (p + q)
      (cochainCup p q α
        (cochainPullback (sInclusion ((U : Set X) ∩ (V : Set X))) q β)) = 0 :=
    cochainCupZMod2_respects_cocycles p q α _ hα hβW
  have hcup : cochainCoboundary (ZMod 2) X (p + 1 + q)
      (cochainCup (p + 1) q γ β) = 0 :=
    cochainCupZMod2_respects_cocycles (p + 1) q γ β hγ hβ
  have hγ' : cochainCoboundary (ZMod 2) X (p + q + 1)
      (cochainCast (aw_degree_left_succ p q) (cochainCup (p + 1) q γ β)) = 0 := by
    rw [cochainCast_coboundary (aw_degree_left_succ p q)
      (show p + 1 + q + 1 = p + q + 1 + 1 by omega), hcup, cochainCast_zero]
  have haUV' : cochainPullback (subInclusion Set.inter_subset_left) (p + q)
        (cochainCup p q aU (cochainPullback (sInclusion (U : Set X)) q β))
      + cochainPullback (subInclusion Set.inter_subset_right) (p + q)
        (cochainCup p q aV (cochainPullback (sInclusion (V : Set X)) q β))
      = cochainCup p q α
        (cochainPullback (sInclusion ((U : Set X) ∩ (V : Set X))) q β) := by
    rw [cochainCup_naturality, cochainCup_naturality, hrestrU, hrestrV,
      ← cochainCup_add_left, haUV]
  have hγU' : cochainPullback (sInclusion (U : Set X)) (p + q + 1)
        (cochainCast (aw_degree_left_succ p q) (cochainCup (p + 1) q γ β))
      = cochainCoboundary (ZMod 2) (TopCat.of (U : Set X)) (p + q)
          (cochainCup p q aU (cochainPullback (sInclusion (U : Set X)) q β)) := by
    rw [cochainCast_pullback, cochainCup_naturality, hγU,
      cochainCupZMod2_differential, hβU, cochainCup_zero_right, cochainCast_zero,
      add_zero]
  have hγV' : cochainPullback (sInclusion (V : Set X)) (p + q + 1)
        (cochainCast (aw_degree_left_succ p q) (cochainCup (p + 1) q γ β))
      = cochainCoboundary (ZMod 2) (TopCat.of (V : Set X)) (p + q)
          (cochainCup p q aV (cochainPullback (sInclusion (V : Set X)) q β)) := by
    rw [cochainCast_pullback, cochainCup_naturality, hγV,
      cochainCupZMod2_differential, hβV, cochainCup_zero_right, cochainCast_zero,
      add_zero]
  -- the value of `δ` on `a`
  have hdelta : (mvDelta U V hUV p).hom a = cocycleClass X (p + 1) γ hγ := by
    rw [← hacls]
    exact mvDelta_spec U V hUV p α hα aU aV haUV γ hγ hγU hγV
  -- the left-hand side as the class of a cochain
  have hLHS : cup a (pull (sInclusion ((U : Set X) ∩ (V : Set X))) q b)
      = cocycleClass (TopCat.of ↥((U : Set X) ∩ (V : Set X))) (p + q)
          (cochainCup p q α
            (cochainPullback (sInclusion ((U : Set X) ∩ (V : Set X))) q β)) hα' := by
    rw [← hacls, ← hb, pull_mk, cup_mk]
  rw [hLHS, mvDelta_spec U V hUV (p + q)
    (cochainCup p q α (cochainPullback (sInclusion ((U : Set X) ∩ (V : Set X))) q β)) hα'
    (cochainCup p q aU (cochainPullback (sInclusion (U : Set X)) q β))
    (cochainCup p q aV (cochainPullback (sInclusion (V : Set X)) q β)) haUV'
    (cochainCast (aw_degree_left_succ p q) (cochainCup (p + 1) q γ β)) hγ' hγU' hγV',
    hdelta, ← hb, cup_mk, cohCast_cocycleClass _ _ _ hγ']

/-- The same statement with the subtype inclusion written as `inclSubtype`, which is
the form `cc-projective`'s Leray–Hirsch rung consumes. -/
theorem mvDelta_cup_inclSubtype (U V : Opens X) (hUV : U ⊔ V = ⊤) {p q : ℕ}
    (a : Hmod2 (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p) (b : Hmod2 X q) :
    (mvDelta U V hUV (p + q)).hom
        (cup a (pull (inclSubtype ((U : Set X) ∩ (V : Set X))) q b))
      = cohCast (show p + 1 + q = p + q + 1 by omega)
          (cup ((mvDelta U V hUV p).hom a) b) :=
  mvDelta_cup U V hUV a b

end MVDelta

end

end GroupApproximation.CharClass
