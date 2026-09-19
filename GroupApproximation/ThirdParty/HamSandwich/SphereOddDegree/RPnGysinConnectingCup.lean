import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnGysinConnectingCupIdentities

/-!
# The Smith/Gysin connecting map is cup product with `actualRPAlpha`

This endpoint packages the cochain identities into the connecting-map formula.
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AlexanderWhitney

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## The connecting-map identity -/

/-- Wiring lemma: given a cocycle `c` and the two cochain identities, the
connecting map sends `[c]` to the class of `cochainCup k 1 c (w1Cochain n)`. -/
theorem rpGysinConnecting_cocycleClass (n k : ℕ)
    (c : singularCochainGroup (ZMod 2) (TopCat.of (RP n)) k)
    (hc : cochainCoboundary (ZMod 2) (TopCat.of (RP n)) k c = 0) :
    (rpGysinConnecting n k).hom (cocycleClass (TopCat.of (RP n)) k c hc)
      = cocycleClass (TopCat.of (RP n)) (k + 1) (cochainCup k 1 c (w1Cochain n))
          (cochainCupZMod2_respects_cocycles k 1 c (w1Cochain n) hc
            (w1Cochain_cocycle n)) := by
  have hSE := transferSEScoch_shortExact n
  have hrel : (ComplexShape.up ℕ).Rel k (k + 1) := rfl
  have hx₃ : ((forget₂ (ModuleCat (ZMod 2)) Ab).map
      ((transferSEScoch n).X₃.d k (k + 1))) c = 0 := hc
  have hg' : ((forget₂ (ModuleCat (ZMod 2)) Ab).map
      ((transferSEScoch n).g.f k)) (gysinLift n k c) = c :=
    transfer_gysinLift n k c
  have hf' : ((forget₂ (ModuleCat (ZMod 2)) Ab).map
      ((transferSEScoch n).f.f (k + 1)))
        (cochainCup k 1 c (w1Cochain n))
      = ((forget₂ (ModuleCat (ZMod 2)) Ab).map
          ((transferSEScoch n).X₂.d k (k + 1))) (gysinLift n k c) :=
    f_cup_eq_coboundary n k c hc
  have key := hSE.δ_apply k (k + 1) hrel c hx₃ (gysinLift n k c) hg'
    (cochainCup k 1 c (w1Cochain n)) hf' (k + 2)
    (by simp [ComplexShape.next])
  rw [rpGysinConnecting_eq_δ]
  exact key

/-- **The Smith/Gysin connecting map is cup product with the canonical class**
`α = actualRPAlpha n`, evaluated pointwise. -/
theorem rpGysinConnecting_eq_cup_actualRPAlpha (n k : ℕ)
    (x : rpCohomology n k) :
    (rpGysinConnecting n k).hom x = cupZMod2 x (actualRPAlpha n) := by
  obtain ⟨c, hc, rfl⟩ := cocycleClass_surjective (TopCat.of (RP n)) k x
  rw [rpGysinConnecting_cocycleClass n k c hc]
  rw [← rpW1Class_eq_actualRPAlpha]
  rw [show rpW1Class n = cocycleClass (TopCat.of (RP n)) 1 (w1Cochain n)
    (w1Cochain_cocycle n) from rfl]
  rw [cupZMod2_mk]

/-- **`simp` form of the connecting-map identity.** -/
@[simp] theorem rpGysinConnecting_apply (n k : ℕ) (x : rpCohomology n k) :
    (rpGysinConnecting n k).hom x = cupZMod2 x (actualRPAlpha n) :=
  rpGysinConnecting_eq_cup_actualRPAlpha n k x

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
