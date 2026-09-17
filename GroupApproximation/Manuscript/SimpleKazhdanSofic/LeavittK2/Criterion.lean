import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CriterionInterfaces
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CriterionGeneration
import GroupApproximation.Meta.AxiomGuard

/-!
# The Steinberg comparison criterion IV: the endpoint (lane sk-leavitt-14)

Carto `sk-leavitt` lane 14 (`LK2/Criterion`), the target of `LeavittFP/K2Endpoints.lean:52`:

  `stab (K₂(3, L)) = ⊥  →  K₂(4, L) = ⊥`.

## Route

Assume `stab (K₂(3, L)) = ⊥`.

1. `RankFourLiftStatement` (lanes 05, 13) gives `σ : J → St_4(L)` with
   `σ(1 + E_{ij}(a)) = x_{ij}(a)` for `j ≠ 3`, satisfying Brown's relations with `T = w_{32}`.
2. `BrownExtensionStatement` (lanes 06–12) extends `σ` to `F : GL_4(L) → St_4(L)` with
   `F τ = w_{32}`.
3. `F ∘ projection` agrees with the identity on `x_{ij}(a)` (`j ≠ 3`) and on `w_{32}`.  These
   generate `St_4(L)` (`steinberg_eq_top_of_mem`), so `F ∘ projection = id` (`lift_projection_eq`).
4. So `projection` has a left inverse, it is injective, and `K₂(4, L) = ⊥` (`K2_eq_bot_iff`).

The two inputs are bundled as `Criterion.RankFourCriterionInputsStatement`.  It is true and
strictly smaller than the target; see `CriterionInterfaces`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

namespace Criterion

open GroupApproximation.BooneHigman.SteinbergBasic

noncomputable section

/-- The loop `St_4(L) → E_4(L) ⊆ GL_4(L) → St_4(L)` through a candidate extension `F`. -/
def projectionLoop (F : GLFour →* St 4 BinL) : St 4 BinL →* St 4 BinL :=
  F.comp ((GroupApproximation.elementaryGroup (Fin 4) BinL).subtype.comp
    GroupApproximation.SteinbergGroup.projection)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion.projectionLoop

/-- **The retraction.**  An extension `F` of a root-lifting `σ` with `F τ = w_{32}` is a left
inverse of `projection`. -/
theorem lift_projection_eq (σ : vertexStab →* St 4 BinL) (F : GLFour →* St 4 BinL)
    (hroot : LiftsRoots σ) (hFJ : ∀ j : vertexStab, F (j : GLFour) = σ j)
    (hFτ : F swapLast = weylLast) (g : St 4 BinL) :
    F ((GroupApproximation.SteinbergGroup.projection g :
      GroupApproximation.elementaryGroup (Fin 4) BinL) : GLFour) = g := by
  have hS : (projectionLoop F).eqLocus (MonoidHom.id (St 4 BinL)) = ⊤ := by
    refine steinberg_eq_top_of_mem _ ?_ ?_
    · intro i j hij hj a
      show F ((GroupApproximation.SteinbergGroup.projection
          (GroupApproximation.SteinbergGroup.x i j hij a) :
            GroupApproximation.elementaryGroup (Fin 4) BinL) : GLFour) =
        GroupApproximation.SteinbergGroup.x i j hij a
      rw [GroupApproximation.SteinbergGroup.projection_x]
      exact (hFJ ⟨GroupApproximation.elementaryUnit i j hij a,
        elementaryUnit_mem_vertexStab i j hij hj a⟩).trans (hroot i j hij hj a)
    · show F swapLast = weylLast
      exact hFτ
  have hg : g ∈ (projectionLoop F).eqLocus (MonoidHom.id (St 4 BinL)) := by
    rw [hS]
    exact Subgroup.mem_top g
  exact hg

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion.lift_projection_eq

end

end Criterion

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Lane sk-leavitt-14 endpoint** (Khanh, Theorem 5.1 at rank four): given Brown's extension
property and the vertex lift (`Criterion.RankFourCriterionInputsStatement`),
`stab (K₂(3, L)) = ⊥` implies `K₂(4, L) = ⊥`. -/
theorem rankFourInjective_of_stabKernelThreeTrivial
    (hin : Criterion.RankFourCriterionInputsStatement) :
    EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement →
      LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement := by
  intro h3
  obtain ⟨hB, hL⟩ := hin
  obtain ⟨σ, hroot, hE, hT⟩ := hL h3
  obtain ⟨F, hFJ, hFτ⟩ := hB σ Criterion.weylLast hE hT
  show K2 (Fin 4) Criterion.BinL = ⊥
  rw [K2_eq_bot_iff]
  intro g g' hgg'
  calc g = F ((GroupApproximation.SteinbergGroup.projection g :
          GroupApproximation.elementaryGroup (Fin 4) Criterion.BinL) : Criterion.GLFour) :=
        (Criterion.lift_projection_eq σ F hroot hFJ hFτ g).symm
    _ = F ((GroupApproximation.SteinbergGroup.projection g' :
          GroupApproximation.elementaryGroup (Fin 4) Criterion.BinL) : Criterion.GLFour) := by
        rw [hgg']
    _ = g' := Criterion.lift_projection_eq σ F hroot hFJ hFτ g'

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rankFourInjective_of_stabKernelThreeTrivial

/-- **Lane 15's interface form.**  The criterion inputs discharge
`EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement`. -/
theorem rankFourInjectiveOfStabKernelThreeTrivial_of_criterionInputs
    (hin : Criterion.RankFourCriterionInputsStatement) :
    EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement :=
  rankFourInjective_of_stabKernelThreeTrivial hin

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rankFourInjectiveOfStabKernelThreeTrivial_of_criterionInputs

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
