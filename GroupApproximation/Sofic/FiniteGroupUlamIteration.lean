import GroupApproximation.Sofic.FiniteGroupUlamStep
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Iterating the finite-group Ulam correction

The quadratic Reynolds--polar step is iterated inside one fixed unital
C-star algebra.  Completeness then produces an exact representation of the
finite group without changing the ambient algebra (and hence without changing
matrix dimension).
-/

namespace GroupApproximation
namespace FiniteGroupUlamIteration

open Filter FiniteGroupUlamStep
open scoped Topology

noncomputable section

universe u v

variable {F : Type u} [Group F] [Fintype F]
variable {A : Type v} [CStarAlgebra A] [Nontrivial A]

/-- The target defect after `n` correction steps. -/
def defectScale (δ : ℝ) : ℕ → ℝ
  | 0 => δ
  | n + 1 => defectScale δ n / 2

theorem defectScale_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) :
    ∀ n, 0 ≤ defectScale δ n := by
  intro n
  induction n with
  | zero => exact hδ0
  | succ n ih =>
      simp only [defectScale]
      positivity

theorem defectScale_le {δ : ℝ} (hδ0 : 0 ≤ δ) :
    ∀ n, defectScale δ n ≤ δ := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      simp only [defectScale]
      have hn := defectScale_nonneg hδ0 n
      linarith

theorem defectScale_eq (δ : ℝ) :
    ∀ n, defectScale δ n = δ * (1 / 2 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => simp [defectScale]
  | succ n ih =>
      rw [defectScale, ih, pow_succ]
      ring

theorem defectScale_tendsto_zero (δ : ℝ) :
    Tendsto (defectScale δ) atTop (𝓝 0) := by
  rw [show defectScale δ = fun n ↦ δ * (1 / 2 : ℝ) ^ n by
    funext n
    exact defectScale_eq δ n]
  have hp : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have hc : Tendsto (fun _n : ℕ ↦ δ) atTop (𝓝 δ) := tendsto_const_nhds
  simpa using hc.mul hp

/-- A unitary table carrying a certified uniform multiplication defect. -/
structure ControlledTable (ε : ℝ) where
  table : F → unitary A
  defect : MultiplicativeDefectAtMost table ε

/-- One controlled correction step, with the defect target halved. -/
def controlledStep {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 52)
    (Φ : ControlledTable (F := F) (A := A) ε) :
    ControlledTable (F := F) (A := A) (ε / 2) := by
  have hsmall : ε ≤ 1 / 8 := by linarith
  have hgram : 4 * ε ^ 2 ≤ 1 / 2 := by nlinarith [sq_nonneg ε]
  have hquadratic : 26 * ε ^ 2 ≤ ε / 2 := by nlinarith
  exact
    { table := correctedTable Φ.table hε0 hsmall Φ.defect
      defect := fun g h ↦
        (correctedTable_multiplicativeDefectAtMost
          Φ.table hε0 hsmall Φ.defect hgram g h).trans hquadratic }

/-- The iterated corrected tables, all in the original C-star algebra. -/
def iterationState (φ : F → unitary A) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 52)
    (hφ : MultiplicativeDefectAtMost φ δ) :
    (n : ℕ) → ControlledTable (F := F) (A := A) (defectScale δ n)
  | 0 => ⟨φ, hφ⟩
  | n + 1 => controlledStep
      (defectScale_nonneg hδ0 n)
      ((defectScale_le hδ0 n).trans hδ)
      (iterationState φ hδ0 hδ hφ n)

/-- Consecutive iterates move geometrically. -/
theorem iterationState_dist_succ_le
    (φ : F → unitary A) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 52)
    (hφ : MultiplicativeDefectAtMost φ δ) (g : F) (n : ℕ) :
    dist ((((iterationState φ hδ0 hδ hφ n).table g : unitary A) : A))
        ((((iterationState φ hδ0 hδ hφ (n + 1)).table g : unitary A) : A)) ≤
      (6 * δ) * (1 / 2 : ℝ) ^ n := by
  rw [dist_eq_norm]
  change ‖(((iterationState φ hδ0 hδ hφ n).table g : unitary A) : A) -
      (((iterationState φ hδ0 hδ hφ (n + 1)).table g : unitary A) : A)‖ ≤ _
  rw [← norm_neg, neg_sub]
  have hmove := norm_correctedTable_sub_le
    (iterationState φ hδ0 hδ hφ n).table
    (defectScale_nonneg hδ0 n)
    (by exact ((defectScale_le hδ0 n).trans hδ).trans (by norm_num))
    (iterationState φ hδ0 hδ hφ n).defect g
  change ‖(((iterationState φ hδ0 hδ hφ (n + 1)).table g : unitary A) : A) -
      (((iterationState φ hδ0 hδ hφ n).table g : unitary A) : A)‖ ≤ _
  exact hmove.trans_eq (by rw [defectScale_eq]; ring)

/-- At every packet element the corrected tables form a Cauchy sequence. -/
theorem iterationState_cauchy
    (φ : F → unitary A) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 52)
    (hφ : MultiplicativeDefectAtMost φ δ) (g : F) :
    CauchySeq (fun n ↦
      (((iterationState φ hδ0 hδ hφ n).table g : unitary A) : A)) :=
  cauchySeq_of_le_geometric (1 / 2 : ℝ) (6 * δ) (by norm_num)
    (iterationState_dist_succ_le φ hδ0 hδ hφ g)

/-- The ambient-algebra limit of the iterated unitary tables. -/
def exactifiedValue (φ : F → unitary A) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 52)
    (hφ : MultiplicativeDefectAtMost φ δ) (g : F) : A :=
  Classical.choose (cauchySeq_tendsto_of_complete
    (iterationState_cauchy φ hδ0 hδ hφ g))

theorem iterationState_tendsto_exactifiedValue
    (φ : F → unitary A) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 52)
    (hφ : MultiplicativeDefectAtMost φ δ) (g : F) :
    Tendsto (fun n ↦
      (((iterationState φ hδ0 hδ hφ n).table g : unitary A) : A)) atTop
      (𝓝 (exactifiedValue φ hδ0 hδ hφ g)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete
    (iterationState_cauchy φ hδ0 hδ hφ g))

/-- The limit remains unitary because both unitary equations are closed. -/
theorem exactifiedValue_mem_unitary
    (φ : F → unitary A) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 52)
    (hφ : MultiplicativeDefectAtMost φ δ) (g : F) :
    exactifiedValue φ hδ0 hδ hφ g ∈ unitary A := by
  let u : ℕ → A := fun n ↦
    (((iterationState φ hδ0 hδ hφ n).table g : unitary A) : A)
  let a : A := exactifiedValue φ hδ0 hδ hφ g
  have hu : Tendsto u atTop (𝓝 a) :=
    iterationState_tendsto_exactifiedValue φ hδ0 hδ hφ g
  have hleftLim : Tendsto (fun n ↦ star (u n) * u n) atTop
      (𝓝 (star a * a)) := hu.star.mul hu
  have hrightLim : Tendsto (fun n ↦ u n * star (u n)) atTop
      (𝓝 (a * star a)) := hu.mul hu.star
  have hleftOne : Tendsto (fun n ↦ star (u n) * u n) atTop (𝓝 (1 : A)) := by
    have heq : (fun n ↦ star (u n) * u n) = fun _n : ℕ ↦ (1 : A) := by
      funext n
      exact Unitary.star_mul_self_of_mem
        ((iterationState φ hδ0 hδ hφ n).table g).prop
    rw [heq]
    exact tendsto_const_nhds
  have hrightOne : Tendsto (fun n ↦ u n * star (u n)) atTop (𝓝 (1 : A)) := by
    have heq : (fun n ↦ u n * star (u n)) = fun _n : ℕ ↦ (1 : A) := by
      funext n
      exact Unitary.mul_star_self_of_mem
        ((iterationState φ hδ0 hδ hφ n).table g).prop
    rw [heq]
    exact tendsto_const_nhds
  exact ⟨tendsto_nhds_unique hleftLim hleftOne,
    tendsto_nhds_unique hrightLim hrightOne⟩

/-- The exactified unitary table. -/
def exactifiedTable (φ : F → unitary A) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 52)
    (hφ : MultiplicativeDefectAtMost φ δ) (g : F) : unitary A :=
  ⟨exactifiedValue φ hδ0 hδ hφ g,
    exactifiedValue_mem_unitary φ hδ0 hδ hφ g⟩

theorem iterationState_tendsto_exactified
    (φ : F → unitary A) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 52)
    (hφ : MultiplicativeDefectAtMost φ δ) (g : F) :
    Tendsto (fun n ↦
      (((iterationState φ hδ0 hδ hφ n).table g : unitary A) : A)) atTop
      (𝓝 (((exactifiedTable φ hδ0 hδ hφ g : unitary A) : A))) :=
  iterationState_tendsto_exactifiedValue φ hδ0 hδ hφ g

/-- The limiting table is exactly multiplicative. -/
theorem exactifiedTable_mul
    (φ : F → unitary A) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 52)
    (hφ : MultiplicativeDefectAtMost φ δ) (g h : F) :
    exactifiedTable φ hδ0 hδ hφ (g * h) =
      exactifiedTable φ hδ0 hδ hφ g * exactifiedTable φ hδ0 hδ hφ h := by
  let u : ℕ → F → A := fun n x ↦
    (((iterationState φ hδ0 hδ hφ n).table x : unitary A) : A)
  let a : F → A := fun x ↦
    (((exactifiedTable φ hδ0 hδ hφ x : unitary A) : A))
  have hu (x : F) : Tendsto (fun n ↦ u n x) atTop (𝓝 (a x)) :=
    iterationState_tendsto_exactified φ hδ0 hδ hφ x
  have hprod : Tendsto (fun n ↦ u n g * u n h) atTop (𝓝 (a g * a h)) :=
    (hu g).mul (hu h)
  have hdist : Tendsto (fun n ↦ dist (u n (g * h)) (u n g * u n h))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
      (Eventually.of_forall fun n ↦ ?_) (defectScale_tendsto_zero δ)
    rw [dist_eq_norm]
    exact (iterationState φ hδ0 hδ hφ n).defect g h
  have hprod' : Tendsto (fun n ↦ u n g * u n h) atTop (𝓝 (a (g * h))) :=
    (hu (g * h)).congr_dist hdist
  apply Subtype.ext
  exact tendsto_nhds_unique hprod' hprod

/-- The exactified representation of the finite group. -/
def exactifiedRepresentation
    (φ : F → unitary A) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 52)
    (hφ : MultiplicativeDefectAtMost φ δ) : F →* unitary A where
  toFun := exactifiedTable φ hδ0 hδ hφ
  map_one' := by
    have hmul := exactifiedTable_mul φ hδ0 hδ hφ (1 : F) 1
    simp only [one_mul] at hmul
    apply Eq.symm
    apply mul_left_cancel (a := exactifiedTable φ hδ0 hδ hφ (1 : F))
    simpa only [mul_one] using hmul
  map_mul' := exactifiedTable_mul φ hδ0 hδ hφ

/-- Exactification moves each packet element by at most `12δ`. -/
theorem norm_exactifiedRepresentation_sub_le
    (φ : F → unitary A) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 52)
    (hφ : MultiplicativeDefectAtMost φ δ) (g : F) :
    ‖(((exactifiedRepresentation φ hδ0 hδ hφ g : unitary A) : A)) -
        ((φ g : unitary A) : A)‖ ≤ 12 * δ := by
  let u : ℕ → A := fun n ↦
    (((iterationState φ hδ0 hδ hφ n).table g : unitary A) : A)
  let a : A := (((exactifiedRepresentation φ hδ0 hδ hφ g : unitary A) : A))
  have hu : Tendsto u atTop (𝓝 a) :=
    iterationState_tendsto_exactified φ hδ0 hδ hφ g
  have htail := dist_le_of_le_geometric_of_tendsto₀
    (r := (1 / 2 : ℝ)) (C := 6 * δ) (f := u)
    (by norm_num) (iterationState_dist_succ_le φ hδ0 hδ hφ g) hu
  change ‖a - ((φ g : unitary A) : A)‖ ≤ 12 * δ
  rw [← dist_eq_norm, dist_comm]
  calc
    dist ((φ g : unitary A) : A) a ≤ (6 * δ) / (1 - (1 / 2 : ℝ)) := by
      simpa [u, a, iterationState] using htail
    _ = 12 * δ := by ring

end

end FiniteGroupUlamIteration
end GroupApproximation
