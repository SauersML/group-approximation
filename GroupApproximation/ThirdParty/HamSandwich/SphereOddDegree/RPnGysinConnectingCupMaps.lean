import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnGysinConnectingCupW1Back

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AlexanderWhitney

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## 4. Evaluation of the two transfer/pullback cochain maps -/

/-- Dualizing the chain transfer is precomposition with its degree map. -/
theorem projTransferCochainMap_f_apply_degree (n k : ℕ)
    (b : singularCochainGroup (ZMod 2) (TopCat.of (Sphere n)) k)
    (x : (chainCxZMod2 (TopCat.of (RP n))).X k) :
    (((projTransferCochainMap n).f k).hom b).hom x
      = b.hom (((projTransferChainMap n).f k).hom x) := by
  change (((projTransferChainMap n).f k ≫ b).hom x) = _
  exact ModuleCat.comp_apply _ _ _

/-
**Evaluation of the cochain transfer** `g = tr*` on a basis simplex.
-/
theorem transferCochain_eval (n k : ℕ) (b : singularCochainGroup (ZMod 2) (TopCat.of (Sphere n)) k)
    (σ : singularSimplices (TopCat.of (RP n)) k) :
    cochainEval k (((transferSEScoch n).g.f k).hom b) σ
      = cochainEval k b (canLift n k σ) + cochainEval k b (sAnti n k (canLift n k σ)) := by
  change cochainEval k (((projTransferCochainMap n).f k).hom b) σ = _
  have hchain := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom (projTransferChainDegree_ι_canLift n k σ))
    (1 : ZMod 2)
  have hdetect := congrArg b.hom hchain
  calc
    cochainEval k (((projTransferCochainMap n).f k).hom b) σ =
        b.hom ((projTransferChainDegree n k).hom
          ((Sigma.ι (fun _ : singularSimplices (TopCat.of (RP n)) k =>
            transferCoeff) σ).hom 1)) :=
      projTransferCochainMap_f_apply_degree n k b _
    _ = _ := by
      simp only [ModuleCat.hom_comp, ModuleCat.hom_add, LinearMap.comp_apply,
        LinearMap.add_apply, map_add] at hdetect
      convert hdetect using 1 <;> rfl

/-- **Evaluation of the pullback** `f = proj*` on a basis simplex. -/
theorem pullbackCochain_eval (n k : ℕ) (ψ : singularCochainGroup (ZMod 2) (TopCat.of (RP n)) k)
    (ρ : singularSimplices (TopCat.of (Sphere n)) k) :
    cochainEval k (((transferSEScoch n).f.f k).hom ψ) ρ
      = cochainEval k ψ (sProj n k ρ) := by
  change cochainEval k (cochainPullback (TopCat.ofHom (proj n)) k ψ) ρ = _
  rw [cochainPullback_eval]
  rfl



end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
