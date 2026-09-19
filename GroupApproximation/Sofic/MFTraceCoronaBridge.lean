import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Analysis.PreliminaryInequalitiesPrinted
import GroupApproximation.Analysis.ShulmanTraceClasses

/-!
# The MF-trace bridge, through the operator-norm corona

`ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal` used to be proved by
way of `IsMFRegularCharacter` and the quantitative corner-and-polar argument
of `Sofic/MFTraceRecognition.lean`.  This file supplies its replacement proof.

The theorem itself stays where it is, with its statement untouched: a second
declaration concluding the same proposition would be a genuine `DUPLICATE`
finding for the kernel audit, not a false positive.  So the last step is taken
in `Sofic/ShulmanMFTraceBridge.lean`, which imports this module and consumes
`exists_injective_coronaUnitaryHom` as the whole of its proof.

## The idea

Let `φ n : A → M_{X n}` witness `IsMFTrace τ`.  The models are uniformly
bounded pointwise, so `n ↦ φ n a` is a bounded matrix sequence; and the three
defect clauses of `MFTraceModel` say exactly that the multiplicative, linear
and adjoint defects tend to zero *in operator norm*.  Dividing by the
operator-norm-null sequences therefore turns the asymptotic homomorphism into
an honest one:

`Φ : A →⋆ₙₐ[ℂ] ∏ M_{X n} / ⊕ M_{X n}`.

Everything after this happens in the corona, where `Φ` is exact.  That is why
no spectral rounding, no inflation, no polar correction and no corank estimate
appear anywhere below: the approximation is discharged once, by the quotient,
rather than tracked through a schedule of accuracies.

`Φ` is not unital -- `p = Φ 1` is only a projection -- and the passage from
`Φ` to a group homomorphism is `g ↦ Φ (u g) + (1 - p)`.  That map is already
in the tree as `nonUnitalStarAlgHomUnitaryMap` (`Analysis/MFAlgebra.lean`),
together with the verification that it is unitary-valued and multiplicative,
so none of it is rebuilt here.

Injectivity is the only place the trace clause is used, and it is
`MFTraceModel.eq_of_coronaHom_eq`: elements with the same corona image have
asymptotically equal models in operator norm, the normalized trace is
contractive for that norm, so their `τ`-values agree.  Since `τ (u g) = 0` for
`g ≠ 1` while `τ 1 = 1`, no nonidentity `g` can have `Θ g = 1`.

## The step the short argument omits

`MFTraceModel.space` carries **no** positivity: nothing in the definition
forbids an empty model, and `IsOperatorMF` demands positive dimensions at
*every* index.  `MFTraceModel.exists_shift` closes this.  At an empty model
the normalized trace divides by zero, which in Lean is zero, so the trace
clause at the unit reads `‖1 - 0‖ = 1` there; since that clause forces the
quantity eventually below `1`, only finitely many models can be empty.
Reindexing by a tail preserves every clause, all of them being limits along
`atTop`.

## What this does not replace

`Sofic/MFTraceRecognition.lean` proves a different, quantitative statement --
a finite test set, an explicit accuracy schedule, a separation constant -- and
other results depend on it, including the two theorems of
`Sofic/ShulmanMFTraceBridge.lean` that this route does not touch.  What
changes is only that the *canonical-maximal* headline no longer routes through
it.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace ShulmanTrace

open Filter Matrix
open scoped Matrix.Norms.L2Operator ENNReal

noncomputable section

universe u

/-! ## Degenerate models -/

/-- At an empty model the normalized trace divides by zero, which is zero. -/
theorem normTrace_of_card_eq_zero (Y : FiniteModel)
    (hY : Fintype.card Y = 0) (B : Matrix Y Y ℂ) : normTrace Y B = 0 := by
  show Matrix.trace B / ((Fintype.card Y : ℕ) : ℂ) = 0
  rw [hY, Nat.cast_zero, div_zero]

section Shift

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-- **Only finitely many models can be empty.**  An empty model reports
normalized trace `0`, so the trace clause at the unit would read `‖1‖ = 1`
there, while that clause forces the quantity eventually below `1`. -/
theorem MFTraceModel.eventually_card_pos {τ : A → ℂ} (M : MFTraceModel τ)
    (hone : τ 1 = 1) :
    ∀ᶠ n in atTop, 0 < Fintype.card (M.space n) := by
  have hlt : ∀ᶠ n in atTop,
      ‖τ 1 - normTrace (M.space n) (M.map n 1)‖ < 1 :=
    (M.tendsto_trace 1).eventually_lt_const one_pos
  filter_upwards [hlt] with n hn
  by_contra hcard
  have hzero : Fintype.card (M.space n) = 0 := by omega
  rw [normTrace_of_card_eq_zero (M.space n) hzero, hone, sub_zero,
    norm_one] at hn
  exact lt_irrefl 1 hn

/-- Reindexing a model by a tail.  Every clause is a limit along `atTop`, and
`fun n ↦ n + N` tends to `atTop`, so all of them survive. -/
def MFTraceModel.shift {τ : A → ℂ} (M : MFTraceModel τ) (N : ℕ) :
    MFTraceModel τ where
  space n := M.space (n + N)
  map n := M.map (n + N)
  tendsto_mul a b := (M.tendsto_mul a b).comp (tendsto_add_atTop_nat N)
  tendsto_linear l m a b :=
    (M.tendsto_linear l m a b).comp (tendsto_add_atTop_nat N)
  tendsto_star a := (M.tendsto_star a).comp (tendsto_add_atTop_nat N)
  bounded a := by
    obtain ⟨C, hC⟩ := M.bounded a
    exact ⟨C, fun n ↦ hC (n + N)⟩
  tendsto_trace a := (M.tendsto_trace a).comp (tendsto_add_atTop_nat N)

/-- **The positive-dimensional model.**  Every MF trace of a unital `τ` has a
matrix model all of whose dimensions are positive. -/
theorem MFTraceModel.exists_shift {τ : A → ℂ} (M : MFTraceModel τ)
    (hone : τ 1 = 1) :
    ∃ M' : MFTraceModel τ, ∀ n, 0 < Fintype.card (M'.space n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (M.eventually_card_pos hone)
  exact ⟨M.shift N, fun n ↦ hN (n + N) (Nat.le_add_left N n)⟩

/-! ### The linear clause, in the three shapes it is used -/

theorem MFTraceModel.tendsto_add {τ : A → ℂ} (M : MFTraceModel τ) (a b : A) :
    Tendsto (fun n ↦ ‖M.map n (a + b) - (M.map n a + M.map n b)‖)
      atTop (nhds 0) := by
  have h := M.tendsto_linear 1 1 a b
  refine h.congr fun n ↦ ?_
  rw [one_smul, one_smul, one_smul, one_smul, sub_sub]

theorem MFTraceModel.tendsto_smul {τ : A → ℂ} (M : MFTraceModel τ) (c : ℂ)
    (a : A) :
    Tendsto (fun n ↦ ‖M.map n (c • a) - c • M.map n a‖) atTop (nhds 0) := by
  have h := M.tendsto_linear c 0 a 0
  refine h.congr fun n ↦ ?_
  rw [zero_smul, add_zero, zero_smul, sub_zero]

theorem MFTraceModel.tendsto_zero_map {τ : A → ℂ} (M : MFTraceModel τ) :
    Tendsto (fun n ↦ ‖M.map n 0 - 0‖) atTop (nhds 0) := by
  have h := M.tendsto_linear 0 0 0 0
  refine h.congr fun n ↦ ?_
  simp

end Shift

/-! ## Killing the defects in the corona -/

section Corona

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

@[simp] theorem coronaQuotient_apply (s : BoundedMatrixSequence (fun n ↦ X n)) :
    normMatrixCStarCoronaQuotient (fun n ↦ X n) s
      = normMatrixCStarCoronaMk (fun n ↦ X n) s := rfl

/-- **The corona kills every operator-norm-null defect.**  This single step
turns each asymptotic clause of `MFTraceModel` into an exact identity. -/
theorem coronaQuotient_eq_of_tendsto_zero
    (s t : BoundedMatrixSequence (fun n ↦ X n))
    (h : Tendsto (fun n ↦ ‖s n - t n‖) atTop (nhds 0)) :
    normMatrixCStarCoronaQuotient (fun n ↦ X n) s =
      normMatrixCStarCoronaQuotient (fun n ↦ X n) t := by
  rw [coronaQuotient_apply, coronaQuotient_apply]
  have hsub : normMatrixCStarCoronaMk (fun n ↦ X n) (s - t) = 0 := by
    rw [normMatrixCStarCoronaMk_eq_zero_iff, IsNullMatrixSequence,
      Nat.cofinite_eq_atTop]
    exact h
  rw [map_sub] at hsub
  exact sub_eq_zero.mp hsub

end Corona

/-! ## The corona homomorphism -/

section CoronaHom

variable {A : Type*} [CStarAlgebra A] {τ : A → ℂ}

/-- The bounded matrix sequence of the models of a single element.  The
`bounded` clause of `MFTraceModel` is exactly membership in `ℓ∞`. -/
def MFTraceModel.seq (M : MFTraceModel τ) (a : A) :
    BoundedMatrixSequence (fun n ↦ M.space n) :=
  ⟨fun n ↦ M.map n a, by
    have hmem : Memℓp (fun n ↦ M.map n a) ∞ := by
      rw [memℓp_infty_iff]
      obtain ⟨C, hC⟩ := M.bounded a
      refine ⟨C, ?_⟩
      rintro x ⟨n, rfl⟩
      exact hC n
    exact hmem⟩

@[simp] theorem MFTraceModel.seq_apply (M : MFTraceModel τ) (a : A) (n : ℕ) :
    M.seq a n = M.map n a := rfl

/-- **The asymptotic homomorphism, made exact.**  The defect clauses of
`MFTraceModel` are precisely the statement that the multiplicative, linear and
adjoint defects are operator-norm null, hence zero in the corona. -/
def MFTraceModel.coronaHom (M : MFTraceModel τ) [∀ n, Nonempty (M.space n)] :
    A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ M.space n) where
  toFun a := normMatrixCStarCoronaQuotient (fun n ↦ M.space n) (M.seq a)
  map_smul' c a := by
    have h : normMatrixCStarCoronaQuotient (fun n ↦ M.space n) (M.seq (c • a))
        = normMatrixCStarCoronaQuotient (fun n ↦ M.space n) (c • M.seq a) :=
      coronaQuotient_eq_of_tendsto_zero _ _ _ (M.tendsto_smul c a)
    rw [h, map_smul]
    rfl
  map_zero' := by
    have h : normMatrixCStarCoronaQuotient (fun n ↦ M.space n) (M.seq 0)
        = normMatrixCStarCoronaQuotient (fun n ↦ M.space n) 0 :=
      coronaQuotient_eq_of_tendsto_zero _ _ _ M.tendsto_zero_map
    rw [h, map_zero]
  map_add' a b := by
    have h : normMatrixCStarCoronaQuotient (fun n ↦ M.space n) (M.seq (a + b))
        = normMatrixCStarCoronaQuotient (fun n ↦ M.space n)
            (M.seq a + M.seq b) :=
      coronaQuotient_eq_of_tendsto_zero _ _ _ (M.tendsto_add a b)
    rw [h, map_add]
  map_mul' a b := by
    have h : normMatrixCStarCoronaQuotient (fun n ↦ M.space n) (M.seq (a * b))
        = normMatrixCStarCoronaQuotient (fun n ↦ M.space n)
            (M.seq a * M.seq b) :=
      coronaQuotient_eq_of_tendsto_zero _ _ _ (M.tendsto_mul a b)
    rw [h, map_mul]
  map_star' a := by
    have h : normMatrixCStarCoronaQuotient (fun n ↦ M.space n)
          (M.seq (star a))
        = normMatrixCStarCoronaQuotient (fun n ↦ M.space n) (star (M.seq a)) :=
      coronaQuotient_eq_of_tendsto_zero _ _ _ (M.tendsto_star a)
    rw [h, map_star]

@[simp] theorem MFTraceModel.coronaHom_apply (M : MFTraceModel τ)
    [∀ n, Nonempty (M.space n)] (a : A) :
    M.coronaHom a =
      normMatrixCStarCoronaQuotient (fun n ↦ M.space n) (M.seq a) := rfl

/-- **The one place the trace clause is used.**  Elements with the same corona
image have asymptotically equal models in operator norm; the normalized trace
is contractive for that norm, so their `τ`-values agree. -/
theorem MFTraceModel.eq_of_coronaHom_eq (M : MFTraceModel τ)
    [∀ n, Nonempty (M.space n)] {a b : A}
    (hab : M.coronaHom a = M.coronaHom b) : τ a = τ b := by
  have hnull : Tendsto (fun n ↦ ‖M.map n a - M.map n b‖) atTop (nhds 0) := by
    have hseq : normMatrixCStarCoronaMk (fun n ↦ M.space n)
        (M.seq a - M.seq b) = 0 := by
      rw [map_sub]
      exact sub_eq_zero_of_eq hab
    rw [normMatrixCStarCoronaMk_eq_zero_iff, IsNullMatrixSequence,
      Nat.cofinite_eq_atTop] at hseq
    exact hseq
  have hta := M.tendsto_trace a
  have htb := M.tendsto_trace b
  have hbound : ∀ n : ℕ,
      ‖τ a - τ b‖ ≤ ‖τ a - normTrace (M.space n) (M.map n a)‖
        + ‖M.map n a - M.map n b‖
        + ‖τ b - normTrace (M.space n) (M.map n b)‖ := by
    intro n
    have hmid : ‖normTrace (M.space n) (M.map n a)
        - normTrace (M.space n) (M.map n b)‖ ≤ ‖M.map n a - M.map n b‖ := by
      rw [← normTrace_sub]
      exact PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm
        (M.space n) (M.map n a - M.map n b)
    have hrev : ‖normTrace (M.space n) (M.map n b) - τ b‖
        = ‖τ b - normTrace (M.space n) (M.map n b)‖ := norm_sub_rev _ _
    calc ‖τ a - τ b‖
        = ‖(τ a - normTrace (M.space n) (M.map n a))
            + (normTrace (M.space n) (M.map n a)
              - normTrace (M.space n) (M.map n b))
            + (normTrace (M.space n) (M.map n b) - τ b)‖ := by
          congr 1
          ring
      _ ≤ ‖(τ a - normTrace (M.space n) (M.map n a))
            + (normTrace (M.space n) (M.map n a)
              - normTrace (M.space n) (M.map n b))‖
          + ‖normTrace (M.space n) (M.map n b) - τ b‖ := norm_add_le _ _
      _ ≤ ‖τ a - normTrace (M.space n) (M.map n a)‖
          + ‖normTrace (M.space n) (M.map n a)
              - normTrace (M.space n) (M.map n b)‖
          + ‖normTrace (M.space n) (M.map n b) - τ b‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ‖τ a - normTrace (M.space n) (M.map n a)‖
          + ‖M.map n a - M.map n b‖
          + ‖τ b - normTrace (M.space n) (M.map n b)‖ := by
          rw [hrev]
          exact add_le_add (add_le_add le_rfl hmid) le_rfl
  have hsum : Tendsto (fun n : ℕ ↦
      ‖τ a - normTrace (M.space n) (M.map n a)‖
        + ‖M.map n a - M.map n b‖
        + ‖τ b - normTrace (M.space n) (M.map n b)‖) atTop (nhds 0) := by
    have h := (hta.add hnull).add htb
    rw [show ((0 : ℝ) + 0 + 0) = 0 by norm_num] at h
    exact h
  have hle : ‖τ a - τ b‖ ≤ 0 := ge_of_tendsto' hsum hbound
  have hzero : τ a - τ b = 0 :=
    norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  linear_combination hzero

end CoronaHom

/-! ## The bridge -/

section Bridge

variable (G : Type u) [Group G]

/-- **The corona route.**  From a positive-dimensional matrix model for the
canonical trace of `C⋆(G)`, an injective homomorphism of `G` into the unitary
sequence corona.

The unitary correction `g ↦ Φ (u g) + (1 - Φ 1)` is
`nonUnitalStarAlgHomUnitaryMap`, already in the tree; only injectivity is
proved here, and it is proved from the trace clause alone. -/
theorem exists_injective_coronaUnitaryHom
    (M : MFTraceModel
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a))
    (hcard : ∀ n, 0 < Fintype.card (M.space n)) :
    ∃ rho : G →* NormMatrixCoronaUnitary M.space, Function.Injective rho := by
  letI : ∀ n, Nonempty (M.space n) := fun n ↦
    Fintype.card_pos_iff.mp (hcard n)
  have hinj : Function.Injective
      ((nonUnitalStarAlgHomUnitaryMap M.coronaHom).comp
        (maximalGroupCStarUnitaryHom G)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    by_contra hgne
    have hval : M.coronaHom (maximalGroupCStarGenerator G g)
        + (1 - M.coronaHom 1) = 1 := congrArg Subtype.val hg
    have hone : M.coronaHom (1 : MaximalGroupCStar G)
        + (1 - M.coronaHom 1) = 1 := by abel
    have heq : M.coronaHom (maximalGroupCStarGenerator G g)
        = M.coronaHom (1 : MaximalGroupCStar G) :=
      add_right_cancel (hval.trans hone.symm)
    have htr := M.eq_of_coronaHom_eq heq
    rw [canonicalMaximalTrace_generator_of_ne_one G hgne,
      canonicalMaximalTrace_one G] at htr
    exact zero_ne_one htr
  exact ⟨(normMatrixCoronaUnitaryEquiv M.space).symm.toMonoidHom.comp
      ((nonUnitalStarAlgHomUnitaryMap M.coronaHom).comp
        (maximalGroupCStarUnitaryHom G)),
    (normMatrixCoronaUnitaryEquiv M.space).symm.injective.comp hinj⟩

/-! This module deliberately stops here, one step short of the conclusion.

Discharging `IsMFTrace → IsOperatorMF` again *here* would state a proposition
already proved as `isOperatorMF_of_isMFTrace_canonicalMaximal`, which the
kernel audit's `DUPLICATE` detector reports and which would be a real finding
rather than a false positive: two declarations, one proposition.  So the last
step is not taken in this file.  `exists_injective_coronaUnitaryHom` is the
whole corona argument, and `Sofic/ShulmanMFTraceBridge.lean` consumes it as
the body of the pinned theorem, whose statement is unchanged. -/

end Bridge

end

end ShulmanTrace
end GroupApproximation
