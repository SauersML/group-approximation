import GroupApproximation.Analysis.LIXLimitCompletion
import GroupApproximation.Analysis.TraciallyCompleteCStar

/-!
# A tracial state on the inductive limit of a tower of C⋆-algebras

Let `T` be a tower of unital C⋆-algebras `A 0 → A 1 → ⋯` (`Analysis/LIXLimitTower`) and suppose
every level carries a tracial state.  Then the inductive limit `T.Limit` carries one.

## The argument

1. **A compatible family, by compactness.**  The trace space of a unital C⋆-algebra is weak-star
   compact (`TraciallyComplete.compactSpace_tracialState`), so the product
   `∏ᵢ T(A i)` is compact.  The families compatible below level `j`,
   `{τ | ∀ i < j, τ i = τ (i+1) ∘ φᵢ}`, form a decreasing sequence of closed sets, and each is
   nonempty: pull one tracial state of `A j` back to the lower levels along the climbing maps and
   fill the higher levels arbitrarily.  Cantor's intersection theorem gives a family compatible at
   every level.
2. **The colimit.**  A compatible family defines a functional on the algebraic colimit,
   `[a] ↦ τ i a` for `a ∈ A i`, well defined because `τ i (climb i k a) = τ k a`.  Every law of a
   tracial state is checked at one common level.
3. **The completion.**  The functional is contractive (a tracial state of a C⋆-algebra has norm
   one), so it extends continuously to the completion, and every law, being an identity or a
   closed condition between continuous functions, passes to the closure of the image.

No functional calculus, no Hahn–Banach, and no fact about the particular tower is used.
-/

namespace GroupApproximation
namespace LIX
namespace CStarTower

universe u

noncomputable section

open TraciallyComplete
open scoped ComplexOrder

variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] (T : CStarTower A)

/-! ### Compatible families of tracial states -/

/-- A family of tracial states, one per level, compatible with the connecting maps. -/
def IsCompatibleTraces (τ : ∀ i, TracialState (A i)) : Prop :=
  ∀ i, τ i = (τ (i + 1)).compStarAlgHom (T.succHom i)

variable {T}

/-- A compatible family is compatible along every climbing map. -/
theorem IsCompatibleTraces.apply_climb {τ : ∀ i, TracialState (A i)}
    (hτ : T.IsCompatibleTraces τ) {k i : ℕ} (h : k ≤ i) (a : A k) :
    τ i (T.climb i k a) = τ k a := by
  induction i, h using Nat.le_induction with
  | base => rw [T.climb_self]
  | succ i h ih =>
    rw [T.climb_succ h, ← ih, hτ i, TracialState.compStarAlgHom_apply]

variable (T)

/-- Weak-star continuity of pulling a tracial state back along a unital ⋆-homomorphism. -/
theorem continuous_compStarAlgHom {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]
    (φ : B →⋆ₐ[ℂ] C) : Continuous fun σ : TracialState C => σ.compStarAlgHom φ := by
  refine (isEmbedding_tracialStateEvaluation (A := B)).isInducing.continuous_iff.mpr ?_
  exact continuous_pi fun b => continuous_tracialState_apply (φ b)

/-- The families of tracial states compatible with the connecting maps below level `j`. -/
def compatibleBelow (j : ℕ) : Set (∀ i, TracialState (A i)) :=
  {τ | ∀ i, i < j → τ i = (τ (i + 1)).compStarAlgHom (T.succHom i)}

theorem mem_compatibleBelow {j : ℕ} {τ : ∀ i, TracialState (A i)} :
    τ ∈ T.compatibleBelow j ↔ ∀ i, i < j → τ i = (τ (i + 1)).compStarAlgHom (T.succHom i) :=
  Iff.rfl

theorem isClosed_compatibleBelow (j : ℕ) : IsClosed (T.compatibleBelow j) := by
  have hEq : T.compatibleBelow j =
      ⋂ i, ⋂ (_ : i < j),
        {τ : ∀ l, TracialState (A l) | τ i = (τ (i + 1)).compStarAlgHom (T.succHom i)} := by
    ext τ
    simp only [compatibleBelow, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hEq]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply i)
      ((continuous_compStarAlgHom (T.succHom i)).comp (continuous_apply (i + 1)))

/-- **Compatible tracial states exist** as soon as every level carries a tracial state: Cantor's
intersection theorem in the compact product of the trace spaces. -/
theorem exists_isCompatibleTraces (hne : ∀ i, Nonempty (TracialState (A i))) :
    ∃ τ : ∀ i, TracialState (A i), T.IsCompatibleTraces τ := by
  haveI : ∀ i, CompactSpace (TracialState (A i)) := fun i => compactSpace_tracialState (A i)
  have hmono : ∀ j, T.compatibleBelow (j + 1) ⊆ T.compatibleBelow j := by
    intro j τ hτ
    exact T.mem_compatibleBelow.mpr fun i hi =>
      (T.mem_compatibleBelow.mp hτ) i (Nat.lt_succ_of_lt hi)
  have hnonempty : ∀ j, (T.compatibleBelow j).Nonempty := by
    intro j
    obtain ⟨σ⟩ := hne j
    refine ⟨fun i => if h : i ≤ j then σ.compStarAlgHom (T.climbHom h)
      else Classical.choice (hne i), T.mem_compatibleBelow.mpr fun i hi => ?_⟩
    have h1 : i ≤ j := hi.le
    have h2 : i + 1 ≤ j := hi
    simp only [dif_pos h1, dif_pos h2]
    apply tracialState_ext
    intro a
    show σ (T.climb j i a) = σ (T.climb j (i + 1) (T.succHom i a))
    rw [← T.climb_succ_self i a, T.climb_trans (Nat.le_add_right i 1) h2 a]
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (T.compatibleBelow) hmono hnonempty (T.isClosed_compatibleBelow 0).isCompact
    (T.isClosed_compatibleBelow)
  refine ⟨τ, fun i => ?_⟩
  exact (T.mem_compatibleBelow.mp (Set.mem_iInter.mp hτ (i + 1))) i (Nat.lt_succ_self i)

/-! ### The tracial state of the algebraic colimit -/

section Colim

variable (τ : ∀ i, TracialState (A i)) (hτ : T.IsCompatibleTraces τ)

/-- The functional on the algebraic colimit determined by a compatible family:
`[a] ↦ τ i a` for `a ∈ A i`. -/
def colimTraceFun : T.Colim → ℂ :=
  Quotient.lift (fun x : Σ n, A n => τ x.1 x.2) (by
    rintro x y ⟨k, hx, hy, e⟩
    show τ x.1 x.2 = τ y.1 y.2
    rw [← hτ.apply_climb hx x.2, ← hτ.apply_climb hy y.2, e])

@[simp] theorem colimTraceFun_mkAt (i : ℕ) (a : A i) :
    T.colimTraceFun τ hτ (T.mkAt i a) = τ i a := rfl

/-- The functional on the colimit, as a complex-linear map. -/
def colimTraceLinearMap : T.Colim →ₗ[ℂ] ℂ where
  toFun := T.colimTraceFun τ hτ
  map_add' := T.ind₂ fun i a b => by
    show T.colimTraceFun τ hτ (T.mkAt i a + T.mkAt i b)
      = T.colimTraceFun τ hτ (T.mkAt i a) + T.colimTraceFun τ hτ (T.mkAt i b)
    rw [T.mkAt_add]
    exact (τ i).map_add a b
  map_smul' c := T.ind fun i a => by
    show T.colimTraceFun τ hτ (c • T.mkAt i a) = (RingHom.id ℂ) c • T.colimTraceFun τ hτ (T.mkAt i a)
    rw [T.mkAt_smul]
    exact (τ i).map_smul c a

/-- **The tracial state of the algebraic colimit.** -/
def colimTracialState : TracialState T.Colim where
  toLinearMap := T.colimTraceLinearMap τ hτ
  map_one := by
    rw [← T.mkAt_one 0]
    exact (τ 0).map_one
  map_star_mul_self_nonneg := T.ind fun i a => by
    show 0 ≤ T.colimTraceFun τ hτ (star (T.mkAt i a) * T.mkAt i a)
    rw [T.mkAt_star, T.mkAt_mul]
    exact (τ i).map_star_mul_self_nonneg a
  map_mul_comm := T.ind₂ fun i a b => by
    show T.colimTraceFun τ hτ (T.mkAt i a * T.mkAt i b)
      = T.colimTraceFun τ hτ (T.mkAt i b * T.mkAt i a)
    rw [T.mkAt_mul, T.mkAt_mul]
    exact (τ i).map_mul_comm a b

/-- The colimit functional is contractive, because each tracial state of a C⋆-algebra is. -/
theorem norm_colimTraceFun_le (z : T.Colim) : ‖T.colimTraceFun τ hτ z‖ ≤ ‖z‖ := by
  obtain ⟨i, a, rfl⟩ := T.exists_mkAt z
  show ‖τ i a‖ ≤ ‖a‖
  exact Manuscript.MFRecognition.TensorSynchronization.norm_tracialState_le (τ i) a

theorem uniformContinuous_colimTraceLinearMap :
    UniformContinuous (T.colimTraceLinearMap τ hτ) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x y hxy
  rw [dist_eq_norm] at hxy
  rw [dist_eq_norm, ← map_sub]
  exact lt_of_le_of_lt (T.norm_colimTraceFun_le τ hτ (x - y)) hxy

end Colim

/-! ### The tracial state of the limit -/

section Limit

variable (τ : ∀ i, TracialState (A i)) (hτ : T.IsCompatibleTraces τ)

/-- The functional on the limit: the continuous extension of the colimit functional to the
completion. -/
def limTraceFun : T.Limit → ℂ :=
  UniformSpace.Completion.extension (T.colimTraceLinearMap τ hτ)

theorem limTraceFun_coe (z : T.Colim) :
    T.limTraceFun τ hτ (z : T.Limit) = T.colimTraceFun τ hτ z :=
  UniformSpace.Completion.extension_coe (T.uniformContinuous_colimTraceLinearMap τ hτ) z

theorem continuous_limTraceFun : Continuous (T.limTraceFun τ hτ) :=
  UniformSpace.Completion.continuous_extension

/-- The limit functional, as a complex-linear map. -/
def limTraceLinearMap : T.Limit →ₗ[ℂ] ℂ where
  toFun := T.limTraceFun τ hτ
  map_add' x y := by
    refine UniformSpace.Completion.induction_on₂ x y (isClosed_eq ?_ ?_) ?_
    · exact (T.continuous_limTraceFun τ hτ).comp continuous_add
    · exact ((T.continuous_limTraceFun τ hτ).comp continuous_fst).add
        ((T.continuous_limTraceFun τ hτ).comp continuous_snd)
    · intro a b
      rw [← UniformSpace.Completion.coe_add, T.limTraceFun_coe τ hτ, T.limTraceFun_coe τ hτ,
        T.limTraceFun_coe τ hτ]
      exact (T.colimTraceLinearMap τ hτ).map_add a b
  map_smul' c x := by
    refine UniformSpace.Completion.induction_on x (isClosed_eq ?_ ?_) ?_
    · exact (T.continuous_limTraceFun τ hτ).comp (continuous_const_smul c)
    · exact (continuous_const_smul _).comp (T.continuous_limTraceFun τ hτ)
    · intro a
      rw [← UniformSpace.Completion.coe_smul, T.limTraceFun_coe τ hτ, T.limTraceFun_coe τ hτ]
      exact (T.colimTraceLinearMap τ hτ).map_smul c a

/-- **The tracial state of the inductive limit** determined by a compatible family. -/
def limTracialState : TracialState T.Limit where
  toLinearMap := T.limTraceLinearMap τ hτ
  map_one := by
    show T.limTraceFun τ hτ 1 = 1
    rw [← UniformSpace.Completion.coe_one, T.limTraceFun_coe τ hτ]
    exact (T.colimTracialState τ hτ).map_one
  map_star_mul_self_nonneg x := by
    refine UniformSpace.Completion.induction_on x ?_ ?_
    · exact isClosed_complexNonneg.preimage
        ((T.continuous_limTraceFun τ hτ).comp
          (CStarCompletion.continuous_star_completion.mul continuous_id))
    · intro a
      show 0 ≤ T.limTraceFun τ hτ (star (a : T.Limit) * (a : T.Limit))
      rw [CStarCompletion.star_coe, ← UniformSpace.Completion.coe_mul, T.limTraceFun_coe τ hτ]
      exact (T.colimTracialState τ hτ).map_star_mul_self_nonneg a
  map_mul_comm x y := by
    refine UniformSpace.Completion.induction_on₂ x y (isClosed_eq ?_ ?_) ?_
    · exact (T.continuous_limTraceFun τ hτ).comp continuous_mul
    · exact (T.continuous_limTraceFun τ hτ).comp (continuous_snd.mul continuous_fst)
    · intro a b
      show T.limTraceFun τ hτ ((a : T.Limit) * (b : T.Limit))
        = T.limTraceFun τ hτ ((b : T.Limit) * (a : T.Limit))
      rw [← UniformSpace.Completion.coe_mul, ← UniformSpace.Completion.coe_mul,
        T.limTraceFun_coe τ hτ, T.limTraceFun_coe τ hτ]
      exact (T.colimTracialState τ hτ).map_mul_comm a b

end Limit

/-- **The inductive limit of a tower whose levels carry tracial states carries a tracial state.** -/
theorem nonempty_tracialState_limit (hne : ∀ i, Nonempty (TracialState (A i))) :
    Nonempty (TracialState T.Limit) := by
  obtain ⟨τ, hτ⟩ := T.exists_isCompatibleTraces hne
  exact ⟨T.limTracialState τ hτ⟩

end

end CStarTower
end LIX
end GroupApproximation
