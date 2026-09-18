import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.UHFUltrapowerUltratrace

/-!
# The trace-kernel extension `0 → J_ω → Q_ω → Q^ω → 0`

Lane `TWWSch3d2Q2` (work order `WO-TWWSch-3d2-Q2`).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. **759** (2020), §4 and Proposition 4.3.

A norm-null sequence is trace-`2`-null, since `‖x_n‖₂ ≤ ‖x_n‖`.  So the quotient
map `ℓ^∞(ℕ, Q) → Q^ω` factors through the norm ultrapower, giving the surjective
⋆-homomorphism `Q_ω → Q^ω`.  Its kernel `J_ω` is the trace-kernel ideal; it is
norm closed because ⋆-homomorphisms of C⋆-algebras are contractive, and hence a
non-unital C⋆-algebra.

## Main declarations

* `qTraceKernelQuotient M ω : QNormCorona Q ω →⋆ₐ[ℂ] QTracialUltrapower M ω`,
  `qTraceKernelQuotient_mk`, `qTraceKernelQuotient_surjective`;
* `qTraceKernel M ω : NonUnitalStarSubalgebra ℂ (QNormCorona Q ω)`,
  `mem_qTraceKernel_iff`, `qNormCoronaMk_mem_qTraceKernel_iff`,
  `isClosed_qTraceKernel`, and the `IsClosed` instance.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter Topology GroupApproximation.PolarLiftingGeneralCStar

noncomputable section

section NormNull

variable {Q : Type} [CStarAlgebra Q] (M : UHFModel Q) (l : Filter ℕ)

/-- **A norm-null sequence is trace-`2`-null**, from `‖x_n‖₂² ≤ ‖x_n‖²`. -/
theorem isQTraceNull_of_isNullCStarSequence {a : BoundedCStarSequence (fun _ : ℕ ↦ Q)}
    (ha : IsNullCStarSequence (fun _ : ℕ ↦ Q) l a) : IsQTraceNull M l a := by
  rw [IsNullCStarSequence] at ha
  rw [IsQTraceNull]
  refine squeeze_zero (fun n ↦ M.re_trace_star_mul_self_nonneg (a n))
    (fun n ↦ (M.re_trace_star_mul_self_le (a n)).trans_eq (sq ‖a n‖)) ?_
  have h := ha.mul ha
  rw [mul_zero] at h
  exact h

end NormNull

section Kernel

variable {Q : Type} [CStarAlgebra Q] [Nontrivial Q] (M : UHFModel Q) (ω : Ultrafilter ℕ)

theorem qTracialUltrapowerMk_eq_zero_of_mem_null (a : BoundedCStarSequence (fun _ : ℕ ↦ Q))
    (ha : a ∈ nullCStarSequenceIdeal (fun _ : ℕ ↦ Q) (ω : Filter ℕ)) :
    qTracialUltrapowerMk M ω a = 0 := by
  rw [qTracialUltrapowerMk_eq_zero_iff]
  exact isQTraceNull_of_isNullCStarSequence M (ω : Filter ℕ)
    ((mem_nullCStarSequenceIdeal_iff (fun _ : ℕ ↦ Q) (ω : Filter ℕ) a).mp ha)

/-- **The quotient `Q_ω → Q^ω`** of the norm ultrapower onto the tracial ultrapower
(Schafhauser 2020, §4). -/
def qTraceKernelQuotient : QNormCorona Q ω →⋆ₐ[ℂ] QTracialUltrapower M ω :=
  CStarTensor.quotientStarLift (nullCStarSequenceIdeal (fun _ : ℕ ↦ Q) (ω : Filter ℕ))
    (qTracialUltrapowerMk M ω) (qTracialUltrapowerMk_eq_zero_of_mem_null M ω)

theorem qTraceKernelQuotient_mk (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    qTraceKernelQuotient M ω (qNormCoronaMk Q ω a) = qTracialUltrapowerMk M ω a :=
  CStarTensor.quotientStarLift_mk _ _ _ a

theorem qTraceKernelQuotient_surjective : Function.Surjective (qTraceKernelQuotient M ω) := by
  intro y
  obtain ⟨a, rfl⟩ := qTracialUltrapowerMk_surjective M ω y
  exact ⟨qNormCoronaMk Q ω a, qTraceKernelQuotient_mk M ω a⟩

/-- The quotient `Q_ω → Q^ω` is continuous, being a ⋆-homomorphism of C⋆-algebras. -/
theorem continuous_qTraceKernelQuotient : Continuous (qTraceKernelQuotient M ω) :=
  AddMonoidHomClass.continuous_of_bound (qTraceKernelQuotient M ω) 1 fun x ↦
    (NonUnitalStarAlgHom.norm_apply_le (qTraceKernelQuotient M ω) x).trans_eq (one_mul _).symm

/-- **The trace-kernel ideal `J_ω`** of `Q_ω`: the kernel of `Q_ω → Q^ω`
(Schafhauser 2020, Proposition 4.3). -/
def qTraceKernel : NonUnitalStarSubalgebra ℂ (QNormCorona Q ω) where
  carrier := {x | qTraceKernelQuotient M ω x = 0}
  add_mem' := fun {x y} (hx : qTraceKernelQuotient M ω x = 0)
      (hy : qTraceKernelQuotient M ω y = 0) ↦
    show qTraceKernelQuotient M ω (x + y) = 0 by rw [map_add, hx, hy, add_zero]
  zero_mem' := map_zero (qTraceKernelQuotient M ω)
  mul_mem' := fun {x y} _ (hy : qTraceKernelQuotient M ω y = 0) ↦
    show qTraceKernelQuotient M ω (x * y) = 0 by rw [map_mul, hy, mul_zero]
  smul_mem' := fun c {x} (hx : qTraceKernelQuotient M ω x = 0) ↦
    show qTraceKernelQuotient M ω (c • x) = 0 by rw [map_smul, hx, smul_zero]
  star_mem' := fun {x} (hx : qTraceKernelQuotient M ω x = 0) ↦
    show qTraceKernelQuotient M ω (star x) = 0 by rw [map_star, hx, star_zero]

theorem mem_qTraceKernel_iff (x : QNormCorona Q ω) :
    x ∈ qTraceKernel M ω ↔ qTraceKernelQuotient M ω x = 0 :=
  Iff.rfl

/-- A class of `Q_ω` lies in `J_ω` exactly when a (any) representative is
trace-`2`-null along `ω`. -/
theorem qNormCoronaMk_mem_qTraceKernel_iff (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    qNormCoronaMk Q ω a ∈ qTraceKernel M ω ↔
      Tendsto (fun n ↦ (M.trace (star (a n) * a n)).re) (ω : Filter ℕ) (𝓝 0) := by
  rw [mem_qTraceKernel_iff, qTraceKernelQuotient_mk, qTracialUltrapowerMk_eq_zero_iff]

/-- **`J_ω` is norm closed.** -/
theorem isClosed_qTraceKernel : IsClosed (qTraceKernel M ω : Set (QNormCorona Q ω)) :=
  isClosed_singleton.preimage (continuous_qTraceKernelQuotient M ω)

instance qTraceKernel_isClosed : IsClosed (qTraceKernel M ω : Set (QNormCorona Q ω)) :=
  isClosed_qTraceKernel M ω

/-- Audit pin: `J_ω` is a non-unital C⋆-algebra. -/
theorem qTraceKernel_hasNonUnitalCStarAlgebra :
    Nonempty (NonUnitalCStarAlgebra (qTraceKernel M ω)) :=
  ⟨inferInstance⟩

end Kernel

end

end GroupApproximation.Full.TWWSchafhauser
