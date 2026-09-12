import GroupApproximation.Manuscript.MFRecognition.HNNTraceCovariantBase
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUniversalDef

/-!
# Density on the HNN edge algebra
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open GroupApproximation.HNNTrace

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- Two star-algebra homomorphisms out of `B₀ = C*(ιρ(S))` that agree
on the represented subgroup agree everywhere. -/
theorem edgeDensity (data : CoronaConjugator G S T phi A X)
    {E : Type} [CStarAlgebra E]
    (f g : sourceEdgeAlgebra data →⋆ₐ[ℂ] E)
    (hfg : ∀ s : S,
      f (((sourceGenerator data s : unitary (sourceEdgeAlgebra data)) :
          sourceEdgeAlgebra data)) =
        g (((sourceGenerator data s : unitary (sourceEdgeAlgebra data)) :
          sourceEdgeAlgebra data))) : f = g := by
  apply DFunLike.ext'
  apply funext
  intro b
  let generators : Set (sourceEdgeAlgebra data) := Set.range fun s : S ↦
    ((sourceGenerator data s : unitary (sourceEdgeAlgebra data)) :
      sourceEdgeAlgebra data)
  have hdense : Dense ((Submodule.span ℂ generators :
      Submodule ℂ (sourceEdgeAlgebra data)) : Set (sourceEdgeAlgebra data)) :=
    groupGeneratedCStar_dense_span ((baseUnitaryHom data).comp S.subtype)
  have hf : Continuous f :=
    (LipschitzWith.of_dist_le_mul (K := 1) fun x y ↦ by
      rw [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub]
      calc
        ‖f (x - y)‖ ≤ ‖x - y‖ := NonUnitalStarAlgHom.norm_apply_le f (x - y)
        _ = dist x y := (dist_eq_norm x y).symm).continuous
  have hg : Continuous g :=
    (LipschitzWith.of_dist_le_mul (K := 1) fun x y ↦ by
      rw [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub]
      calc
        ‖g (x - y)‖ ≤ ‖x - y‖ := NonUnitalStarAlgHom.norm_apply_le g (x - y)
        _ = dist x y := (dist_eq_norm x y).symm).continuous
  have hclosed : IsClosed {x : sourceEdgeAlgebra data | f x = g x} :=
    isClosed_eq hf hg
  have hspan : ((Submodule.span ℂ generators :
      Submodule ℂ (sourceEdgeAlgebra data)) : Set (sourceEdgeAlgebra data)) ⊆
      {x : sourceEdgeAlgebra data | f x = g x} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨s, rfl⟩ := hx
        exact hfg s
    | zero =>
        change f 0 = g 0
        rw [map_zero, map_zero]
    | add x y _ _ hx hy =>
        change f (x + y) = g (x + y)
        rw [map_add, map_add, hx, hy]
    | smul c x _ hx =>
        change f (c • x) = g (c • x)
        rw [map_smul, map_smul, hx]
  exact closure_minimal hspan hclosed (by rw [hdense.closure_eq]; trivial)

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
