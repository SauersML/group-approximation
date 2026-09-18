import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionUHF
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionUHFLift
import GroupApproximation.Sofic.PrintedPreliminaryEstimates

/-!
# From a ucp lift into `Q_ω` to ucp models into `Q`

Lane `TWWSchafhauser-3d1` (work order `WO-TWWSchafhauser-3d-1`).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. **759** (2020), 291--304, §5.

This file joins two landed pieces:

* `ProductCoronaLift A Q l` (`ObstructionUHFLift.lean`): a unital `⋆`-homomorphism
  `ψ : A → Q_l` with a ucp lift `L : A → ℓ^∞(ℕ, Q)`;
* `UHFFilterModel M τ l` (`ObstructionUHF.lean`): ucp maps `A → Q` that are
  asymptotically multiplicative and whose `Q`-traces converge to `τ`.

It needs one estimate: the trace of `Q` is contractive, `|tr_Q(x)| ≤ ‖x‖`,
because `tr_Q = tr_{m!} ∘ E_m` with `E_m` contractive.  Suppose some
representative of `ψ a` has `Q`-traces converging to `τ a` along `l`.  Then the
coordinates of the ucp lift form a `UHFFilterModel`, and at an ultrafilter `τ` is
a locally quasidiagonal trace.

## Main declarations

* `UHFModel.norm_trace_le`, `UHFModel.nontrivial`.
* `ProductCoronaLift.toUHFFilterModel`.
* `hasUHFFilterModel_of_productCoronaLift`,
  `isLocallyQuasidiagonalTrace_of_productCoronaLift`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter GroupApproximation.PolarLiftingGeneralCStar GroupApproximation.Quasidiagonal
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

namespace UHFModel

variable {Q : Type} [CStarAlgebra Q] (M : UHFModel Q)

/-- **The trace of `Q` is contractive**: `tr_Q = tr_{1!} ∘ E_0`, with the
normalized trace contractive for the operator norm and `E_0` contractive. -/
theorem norm_trace_le (x : Q) : ‖M.trace x‖ ≤ ‖x‖ := by
  rw [M.trace_eq 0 x]
  exact (PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm (uhfLevel 0)
    (M.expect 0 x)).trans (M.norm_expect_le 0 x)

/-- The contraction estimate in the form `‖tr_Q x‖ ≤ 1 * ‖x‖`. -/
theorem norm_trace_le_one_mul (x : Q) : ‖M.trace x‖ ≤ 1 * ‖x‖ := by
  rw [one_mul]
  exact M.norm_trace_le x

/-- A C⋆-algebra carrying a UHF model is nontrivial, since its trace is unital. -/
theorem nontrivial : Nontrivial Q := by
  refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
  have h1 := M.trace_one
  rw [← h, _root_.map_zero] at h1
  exact zero_ne_one h1

end UHFModel

namespace ProductCoronaLift

variable {Q : Type} [CStarAlgebra Q] [Nontrivial Q] {A : Type u} [CStarAlgebra A]
  {l : Filter ℕ}

/-- **A ucp lift into `Q_l` gives ucp models into `Q`** (Schafhauser, Crelle 759
(2020), §5).  The maps are the coordinates `φ_n = ev_n ∘ L` of the ucp lift.  Take
any representative `seq a` of `ψ a` whose `Q`-traces converge to `τ a` along `l`;
the traces of the `φ_n` then converge to `τ` as well. -/
def toUHFFilterModel (M : UHFModel Q) (τ : A → ℂ) (L : ProductCoronaLift A Q l)
    (seq : A → BoundedCStarSequence (fun _ : ℕ ↦ Q))
    (hseq : ∀ a : A, cStarProductCoronaQuotient (fun _ : ℕ ↦ Q) l (seq a) = L.hom a)
    (htr : ∀ a : A, Tendsto (fun n ↦ ‖τ a - M.trace (seq a n)‖) l (nhds 0)) :
    UHFFilterModel M τ l where
  map := L.coordMap
  map_one := L.coordMap_one
  completelyPositive := L.completelyPositive_coordMap
  tendsto_mul := L.tendsto_coordMap_mul
  tendsto_trace := L.tendsto_trace_coordMap M.trace 1 M.norm_trace_le_one_mul τ seq hseq htr

end ProductCoronaLift

/-- The existential form: a ucp lift into `Q_ω` at an ultrafilter `ω`, together with
representatives carrying the trace, gives `HasUHFFilterModel M τ`. -/
theorem hasUHFFilterModel_of_productCoronaLift {Q : Type} [CStarAlgebra Q] [Nontrivial Q]
    {A : Type u} [CStarAlgebra A] (M : UHFModel Q) (τ : A → ℂ) (ω : Ultrafilter ℕ)
    (L : ProductCoronaLift A Q (ω : Filter ℕ))
    (seq : A → BoundedCStarSequence (fun _ : ℕ ↦ Q))
    (hseq : ∀ a : A,
      cStarProductCoronaQuotient (fun _ : ℕ ↦ Q) (ω : Filter ℕ) (seq a) = L.hom a)
    (htr : ∀ a : A, Tendsto (fun n ↦ ‖τ a - M.trace (seq a n)‖) (ω : Filter ℕ) (nhds 0)) :
    HasUHFFilterModel M τ :=
  ⟨ω, ⟨L.toUHFFilterModel M τ seq hseq htr⟩⟩

/-- **A ucp lift into `Q_ω` inducing `τ` makes `τ` locally quasidiagonal**
(Schafhauser, Crelle 759 (2020), §§4--5, the last step). -/
theorem isLocallyQuasidiagonalTrace_of_productCoronaLift {Q : Type} [CStarAlgebra Q]
    [Nontrivial Q] {A : Type u} [CStarAlgebra A] (M : UHFModel Q) (τ : A → ℂ)
    (ω : Ultrafilter ℕ) (L : ProductCoronaLift A Q (ω : Filter ℕ))
    (seq : A → BoundedCStarSequence (fun _ : ℕ ↦ Q))
    (hseq : ∀ a : A,
      cStarProductCoronaQuotient (fun _ : ℕ ↦ Q) (ω : Filter ℕ) (seq a) = L.hom a)
    (htr : ∀ a : A, Tendsto (fun n ↦ ‖τ a - M.trace (seq a n)‖) (ω : Filter ℕ) (nhds 0)) :
    IsLocallyQuasidiagonalTrace τ :=
  isLocallyQuasidiagonalTrace_of_hasUHFFilterModel
    (hasUHFFilterModel_of_productCoronaLift M τ ω L seq hseq htr)

end

end GroupApproximation.Full.TWWSchafhauser
