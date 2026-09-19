import GroupApproximation.CharClass.BundleFrame

/-!
# The rank is at most the index size

A projection's rank cannot exceed the dimension it lives in.  The class
identification needs it, because the Euler class is computed at an index chosen from
the bundle's own index type and the comparison has to reach the fibre's rank.

The proof is the frame, not the trace.  `stdFrame` is an isometry from the rank into
the index type, so the induced linear map is injective and the dimensions compare;
nothing analytic about the trace is needed.

## Main declarations

* `rank_le_card` — **the rank is at most the index size**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace Bundle

open scoped Matrix

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The rank is at most the index size**, because the standard frame is an
isometry from the rank into the index type. -/
theorem rank_le_card (q : Bundle X ι) (x : X) : q.rank x ≤ Fintype.card ι := by
  classical
  set W := stdFrame (q.isStarProjection x) (q.rank x) (trace_eq_rank q x) with hW
  have hiso : Wᴴ * W = (1 : Matrix (Fin (q.rank x)) (Fin (q.rank x)) ℂ) :=
    stdFrame_conjTranspose_mul (q.isStarProjection x) (q.rank x) _
  have hinj : Function.Injective (Matrix.mulVecLin W) := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
    have h0 : W *ᵥ v = 0 := hv
    have := congrArg (fun u => Wᴴ *ᵥ u) h0
    simpa [Matrix.mulVec_mulVec, hiso] using this
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using hle

end

end Bundle
end CharClass
end GroupApproximation
