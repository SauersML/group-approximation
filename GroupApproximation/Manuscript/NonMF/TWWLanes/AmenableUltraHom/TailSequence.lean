import GroupApproximation.Analysis.TikuisisWhiteWinterCore
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Analysis.GoldbringHartRoute
import GroupApproximation.Meta.AxiomGuard

/-!
# Amenable trace models as bounded matrix sequences (lane nm-tww-06, part 1)

No census row: this lane is infrastructure for Schafhauser's proof of the
Tikuisis--White--Winter theorem (Brown--Ozawa, Ch. 6).  Its manuscript content
is one sentence: *an amenable trace gives a unital, trace-preserving
⋆-homomorphism `A → ∏_ω M_{k(n)}(ℂ)`, and it is injective if the trace is
faithful*.

## Truth check (read this first)

**The printed lane target is FALSE as stated.**  `IsAmenableTrace τ` puts no
normalization on `τ`.  Take every model empty, with the zero map.  Then
`normTrace` is `0` and `hsNorm` is `0`, so `τ = 0` is amenable.  But every
ultratrace has `ultratrace 1 = 1` (`TracialUltraproduct.ultratrace_one`), so a
unital ⋆-homomorphism cannot carry `0` to `τ`.  Amenability forces
`τ 1 ∈ {0, 1}`.  **The corrected statement adds `hone : τ 1 = 1`.**  A
`FaithfulTracialState` has this for free.  The lane's `X : ℕ → Type` binders
are replaced by the corpus binders `X : ℕ → FiniteModel` with
`∀ n, Nonempty (X n)`, as in `GoldbringHartRoute.IsTraciallyMatrixEmbeddable`.

## Route (this file)

* `exists_tail_card_pos`: when `τ 1 = 1` the models are eventually nonempty.
  This follows the corpus pattern of `AmenableTraceHyperlinear.eventually_card_pos`.
* `tailSpace M N` and `tailSeq M N a`: shift the model past `N` and form the
  bounded sequence `(φ_{n+N} a)_n`.  It is bounded by `‖a‖` (`ucp_norm_le`).
  The sequence is exactly linear and `⋆`-preserving (`ucp_map_star`).  Its
  multiplicative defect is `‖·‖₂`-null (`tendsto_mul_hs`, shifted).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace AmenableUltraHom

open Filter
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

variable {A : Type u} [CStarAlgebra A] {τ : A → ℂ}
variable (M : Quasidiagonal.AmenableTraceModel τ)

/-- **A normalized amenable trace has eventually nonempty models.**  An empty
model has normalized trace `0`, but the trace clause at `1` forces it to be
within `1` of `τ 1 = 1`. -/
theorem exists_tail_card_pos (hone : τ 1 = 1) :
    ∃ K : ℕ, ∀ n, K ≤ n → 0 < Fintype.card (M.space n) := by
  have hlt : ∀ᶠ n in atTop,
      ‖τ 1 - normTrace (M.space n) (M.map n 1)‖ < 1 :=
    (M.tendsto_trace 1).eventually_lt_const one_pos
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hlt
  refine ⟨K, fun n hn ↦ ?_⟩
  have hn' := hK n hn
  by_contra hcard
  have hzero : Fintype.card (M.space n) = 0 := by omega
  have hnt : normTrace (M.space n) (M.map n 1) = 0 := by
    show Matrix.trace (M.map n 1)
      / ((Fintype.card (M.space n) : ℕ) : ℂ) = 0
    rw [hzero, Nat.cast_zero, div_zero]
  rw [hnt, hone, sub_zero, norm_one] at hn'
  exact lt_irrefl 1 hn'

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.exists_tail_card_pos

variable (N : ℕ)

/-- The models shifted past index `N`. -/
abbrev tailSpace : ℕ → FiniteModel := fun n ↦ M.space (n + N)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.tailSpace

/-- The bounded matrix sequence `(φ_{n+N} a)_n`, bounded by `‖a‖` because
each `φ_n` is unital and completely positive. -/
def tailSeq (a : A) : TracialUltraproduct.ModelBoundedSequence (tailSpace M N) :=
  ⟨fun n ↦ M.map (n + N) a, memℓp_infty_iff.mpr ⟨‖a‖, by
    rintro _ ⟨n, rfl⟩
    exact Quasidiagonal.ucp_norm_le (M.map (n + N)) (M.map_one (n + N))
      (M.completelyPositive (n + N)) a⟩⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.tailSeq

theorem tailSeq_zero : tailSeq M N 0 = 0 := by
  refine lp.ext (funext fun n ↦ ?_)
  change M.map (n + N) 0 = 0
  exact map_zero (M.map (n + N))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.tailSeq_zero

theorem tailSeq_add (a b : A) :
    tailSeq M N (a + b) = tailSeq M N a + tailSeq M N b := by
  refine lp.ext (funext fun n ↦ ?_)
  change M.map (n + N) (a + b) = M.map (n + N) a + M.map (n + N) b
  exact map_add (M.map (n + N)) a b

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.tailSeq_add

theorem tailSeq_smul (c : ℂ) (a : A) :
    tailSeq M N (c • a) = c • tailSeq M N a := by
  refine lp.ext (funext fun n ↦ ?_)
  change M.map (n + N) (c • a) = c • M.map (n + N) a
  exact map_smul (M.map (n + N)) c a

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.tailSeq_smul

theorem tailSeq_star (a : A) :
    tailSeq M N (star a) = star (tailSeq M N a) := by
  refine lp.ext (funext fun n ↦ ?_)
  change M.map (n + N) (star a) = star (M.map (n + N) a)
  rw [Matrix.star_eq_conjTranspose]
  exact Quasidiagonal.ucp_map_star (M.map (n + N)) (M.map_one (n + N))
    (M.completelyPositive (n + N)) a

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.tailSeq_star

/-- The shifted multiplicative defect is `‖·‖₂`-null. -/
theorem tendsto_hsNorm_tailSeq_mul (a b : A) :
    Tendsto (fun n ↦ hsNorm (tailSpace M N n)
      (M.map (n + N) (a * b) - M.map (n + N) a * M.map (n + N) b))
      atTop (nhds 0) :=
  (tendsto_add_atTop_iff_nat (f := fun n ↦
      hsNorm (M.space n) (M.map n (a * b) - M.map n a * M.map n b)) N).mpr
    (M.tendsto_mul_hs a b)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.tendsto_hsNorm_tailSeq_mul

end

end AmenableUltraHom
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
