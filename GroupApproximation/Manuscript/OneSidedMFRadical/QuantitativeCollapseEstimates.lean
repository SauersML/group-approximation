import GroupApproximation.Sofic.CliffordBSAmenableMF
import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv

/-!
# Quantitative collapse: the elementary unitary estimates

`non_mf_groups_exist.tex`, the quantitative strengthening of the sentence
"a full MF radical kills every homomorphism to an MF group"
(`thm:quantitative-collapse`).  This module carries step (iii) of its proof:
the three elementary estimates for unitary matrices, in the operator norm the
corona modules use.

* `opLength_commutator_le` — `‖⁅A,B⁆ - 1‖ ≤ 2‖A - 1‖‖B - 1‖`, from the identity
  `AB - BA = (A-1)(B-1) - (B-1)(A-1)` and unitary invariance of the norm.
* `exists_word_bound` — for each word `w` of the free group on `m` letters
  there is a constant `L(w) ≥ 0` with `‖w(U) - 1‖ ≤ L(w) · t` whenever every
  `‖U i - 1‖ ≤ t`, uniformly in the matrix coordinates.  The constant is
  produced by the free-group induction, so it is the word length of whatever
  spelling the induction meets; no claim of minimality is made.
* `exists_commutatorList_bound` — the quadratic bound for a product of
  commutators of words.
* `exists_collapse_constant` — **inequality (1)** of the printed proof: if
  `w i` is the relation `x_i⁻¹ ∏_k ⁅a_{ik}, b_{ik}⁆`, then every generator
  defect is at most `δ + B · t²`, where `δ` bounds the relation defects and
  `t` bounds the generator defects.

Everything is stated with `opLength`, the repository's operator-norm
displacement `‖u - 1‖` of a unitary over a `FiniteModel`; the printed
statement's `M_d(ℂ)` is the model `naturalFiniteModel d`, and
`opLength_naturalFiniteModel` is the (definitional) bridge.

Nothing here mentions the MF radical: these are inequalities about unitary
matrices alone, valid in every coordinate size.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace QuantitativeCollapse

open Matrix
open scoped Matrix.Norms.L2Operator
open scoped commutatorElement

variable {m : ℕ}

/-! ## The printed matrix algebra `M_d(ℂ)` -/

/-- Operator-norm displacement at the natural model `M_d(ℂ)` is literally the
printed quantity `‖U - 1‖`. -/
theorem opLength_naturalFiniteModel (d : ℕ)
    (u : Matrix.unitaryGroup (naturalFiniteModel d) ℂ) :
    opLength (naturalFiniteModel d) u = ‖(u : Matrix (Fin d) (Fin d) ℂ) - 1‖ :=
  rfl

/-! ## The two elementary estimates -/

/-- A unitary is at operator-norm distance at most `2` from the identity. -/
theorem opLength_le_two (Y : FiniteModel) [Nonempty Y]
    (u : Matrix.unitaryGroup Y ℂ) : opLength Y u ≤ 2 := by
  have h1 : ‖(u : Matrix Y Y ℂ)‖ = 1 := CStarRing.norm_of_mem_unitary u.2
  have h2 : ‖(1 : Matrix Y Y ℂ)‖ = 1 := norm_one
  calc opLength Y u = ‖(u : Matrix Y Y ℂ) - 1‖ := rfl
    _ ≤ ‖(u : Matrix Y Y ℂ)‖ + ‖(1 : Matrix Y Y ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [h1, h2]; norm_num

/-- **The commutator estimate.**  `‖⁅A,B⁆ - 1‖ = ‖AB - BA‖ ≤ 2‖A-1‖‖B-1‖`. -/
theorem opLength_commutator_le (Y : FiniteModel) (u v : Matrix.unitaryGroup Y ℂ) :
    opLength Y ⁅u, v⁆ ≤ 2 * (opLength Y u * opLength Y v) := by
  rw [CliffordBSAmenableMF.opLength_commutator]
  have hexp : (u : Matrix Y Y ℂ) * (v : Matrix Y Y ℂ)
        - (v : Matrix Y Y ℂ) * (u : Matrix Y Y ℂ)
      = ((u : Matrix Y Y ℂ) - 1) * ((v : Matrix Y Y ℂ) - 1)
        - ((v : Matrix Y Y ℂ) - 1) * ((u : Matrix Y Y ℂ) - 1) := by
    noncomm_ring
  rw [hexp]
  calc ‖((u : Matrix Y Y ℂ) - 1) * ((v : Matrix Y Y ℂ) - 1)
        - ((v : Matrix Y Y ℂ) - 1) * ((u : Matrix Y Y ℂ) - 1)‖
      ≤ ‖((u : Matrix Y Y ℂ) - 1) * ((v : Matrix Y Y ℂ) - 1)‖
        + ‖((v : Matrix Y Y ℂ) - 1) * ((u : Matrix Y Y ℂ) - 1)‖ := norm_sub_le _ _
    _ ≤ ‖(u : Matrix Y Y ℂ) - 1‖ * ‖(v : Matrix Y Y ℂ) - 1‖
        + ‖(v : Matrix Y Y ℂ) - 1‖ * ‖(u : Matrix Y Y ℂ) - 1‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * (opLength Y u * opLength Y v) := by
        simp only [opLength]; ring

/-! ## The word-length bound -/

/-- **The word estimate.**  Every word of the free group on `Fin m` has a
displacement budget: a constant `L ≥ 0` with `‖w(U) - 1‖ ≤ L · t` in every
coordinate size, for every unitary assignment whose generator defects are at
most `t`.

The constant is produced by the free-group induction, hence depends only on
the word and not on the matrices. -/
theorem exists_word_bound (w : FreeGroup (Fin m)) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (Y : FiniteModel) (U : Fin m → Matrix.unitaryGroup Y ℂ) (t : ℝ),
        (∀ i, opLength Y (U i) ≤ t) →
          opLength Y (FreeGroup.lift U w) ≤ L * t := by
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · refine ⟨0, le_rfl, ?_⟩
    intro Y U t _
    rw [map_one, opLength_one, zero_mul]
  · intro x
    refine ⟨1, zero_le_one, ?_⟩
    intro Y U t ht
    rw [FreeGroup.lift_apply_of, one_mul]
    exact ht x
  · rintro x ⟨L, hL, hb⟩
    refine ⟨L, hL, ?_⟩
    intro Y U t ht
    rw [map_inv, opLength_inv]
    exact hb Y U t ht
  · rintro a b ⟨La, hLa, ha⟩ ⟨Lb, hLb, hb⟩
    refine ⟨La + Lb, by linarith, ?_⟩
    intro Y U t ht
    rw [map_mul]
    calc opLength Y (FreeGroup.lift U a * FreeGroup.lift U b)
        ≤ opLength Y (FreeGroup.lift U a) + opLength Y (FreeGroup.lift U b) :=
          opLength_mul_le Y _ _
      _ ≤ La * t + Lb * t := add_le_add (ha Y U t ht) (hb Y U t ht)
      _ = (La + Lb) * t := (add_mul _ _ _).symm

/-- **The quadratic estimate for a product of commutators of words.**  A finite
list of pairs of words has a budget `B ≥ 0` with
`‖∏_k ⁅a_k(U), b_k(U)⁆ - 1‖ ≤ B · t²` whenever every generator defect is at
most `t`. -/
theorem exists_commutatorList_bound
    (l : List (FreeGroup (Fin m) × FreeGroup (Fin m))) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (Y : FiniteModel) (U : Fin m → Matrix.unitaryGroup Y ℂ) (t : ℝ), 0 ≤ t →
        (∀ i, opLength Y (U i) ≤ t) →
          opLength Y (FreeGroup.lift U (l.map fun p ↦ ⁅p.1, p.2⁆).prod)
            ≤ B * t ^ 2 := by
  induction l with
  | nil =>
      refine ⟨0, le_rfl, ?_⟩
      intro Y U t _ _
      simp
  | cons p l ih =>
      obtain ⟨B, hB, hbound⟩ := ih
      obtain ⟨La, hLa, ha⟩ := exists_word_bound (m := m) p.1
      obtain ⟨Lb, hLb, hb⟩ := exists_word_bound (m := m) p.2
      refine ⟨2 * (La * Lb) + B, by linarith [mul_nonneg hLa hLb], ?_⟩
      intro Y U t ht hU
      have hA : opLength Y (FreeGroup.lift U p.1) ≤ La * t := ha Y U t hU
      have hB' : opLength Y (FreeGroup.lift U p.2) ≤ Lb * t := hb Y U t hU
      have hBnn : 0 ≤ opLength Y (FreeGroup.lift U p.2) := opLength_nonneg _ _
      have hcomm : opLength Y (FreeGroup.lift U ⁅p.1, p.2⁆) ≤ 2 * (La * Lb) * t ^ 2 := by
        rw [map_commutatorElement]
        refine (opLength_commutator_le Y _ _).trans ?_
        have hmul : opLength Y (FreeGroup.lift U p.1) * opLength Y (FreeGroup.lift U p.2)
            ≤ (La * t) * (Lb * t) :=
          mul_le_mul hA hB' hBnn (mul_nonneg hLa ht)
        nlinarith [hmul]
      have hrest := hbound Y U t ht hU
      have hprod : (List.map (fun p ↦ ⁅p.1, p.2⁆) (p :: l)).prod
          = ⁅p.1, p.2⁆ * (List.map (fun p ↦ ⁅p.1, p.2⁆) l).prod := by
        simp
      rw [hprod, map_mul]
      calc opLength Y (FreeGroup.lift U ⁅p.1, p.2⁆
            * FreeGroup.lift U (List.map (fun p ↦ ⁅p.1, p.2⁆) l).prod)
          ≤ opLength Y (FreeGroup.lift U ⁅p.1, p.2⁆)
            + opLength Y (FreeGroup.lift U (List.map (fun p ↦ ⁅p.1, p.2⁆) l).prod) :=
            opLength_mul_le Y _ _
        _ ≤ 2 * (La * Lb) * t ^ 2 + B * t ^ 2 := add_le_add hcomm hrest
        _ = (2 * (La * Lb) + B) * t ^ 2 := by ring

/-! ## Inequality (1) -/

/-- **Inequality (1) of the printed proof.**  Suppose each generator `x_i` of
the free group is written as `w i · ∏_k ⁅a_{ik}, b_{ik}⁆` up to the relation
`w i`, that is `w i = x_i⁻¹ ∏_k ⁅a_{ik}, b_{ik}⁆`.  Then there is a constant
`B ≥ 0`, depending only on the chosen words, such that in every coordinate
size and for every unitary assignment,

`‖U i - 1‖ ≤ δ + B · t²`

whenever `δ` bounds the defects of the relations `w i` and `t` bounds the
generator defects `‖U j - 1‖`. -/
theorem exists_collapse_constant
    (w : Fin m → FreeGroup (Fin m))
    (l : Fin m → List (FreeGroup (Fin m) × FreeGroup (Fin m)))
    (hw : ∀ i, w i = (FreeGroup.of i)⁻¹ * ((l i).map fun p ↦ ⁅p.1, p.2⁆).prod) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (Y : FiniteModel) (U : Fin m → Matrix.unitaryGroup Y ℂ) (t δ : ℝ), 0 ≤ t →
        (∀ j, opLength Y (U j) ≤ t) →
        (∀ j, opLength Y (FreeGroup.lift U (w j)) ≤ δ) →
          ∀ i, opLength Y (U i) ≤ δ + B * t ^ 2 := by
  classical
  choose Bf hBf0 hBf using fun i ↦ exists_commutatorList_bound (m := m) (l i)
  refine ⟨∑ i, Bf i, Finset.sum_nonneg fun i _ ↦ hBf0 i, ?_⟩
  intro Y U t δ ht hU hw' i
  have hle : Bf i ≤ ∑ j, Bf j :=
    Finset.single_le_sum (f := Bf) (fun j _ ↦ hBf0 j) (Finset.mem_univ i)
  have hof : (FreeGroup.of i : FreeGroup (Fin m))
      = ((l i).map fun p ↦ ⁅p.1, p.2⁆).prod * (w i)⁻¹ := by
    rw [hw i, _root_.mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  have hUi : U i = FreeGroup.lift U (FreeGroup.of i) :=
    (FreeGroup.lift_apply_of (f := U) (x := i)).symm
  have hstep : opLength Y (FreeGroup.lift U (FreeGroup.of i)) ≤ Bf i * t ^ 2 + δ := by
    rw [hof, map_mul, map_inv]
    refine (opLength_mul_le Y _ _).trans ?_
    rw [opLength_inv]
    exact add_le_add (hBf i Y U t ht hU) (hw' i)
  have hquad : Bf i * t ^ 2 ≤ (∑ j, Bf j) * t ^ 2 := by
    have : (0 : ℝ) ≤ t ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right hle this
  calc opLength Y (U i) = opLength Y (FreeGroup.lift U (FreeGroup.of i)) := by rw [← hUi]
    _ ≤ Bf i * t ^ 2 + δ := hstep
    _ ≤ (∑ j, Bf j) * t ^ 2 + δ := by linarith
    _ = δ + (∑ j, Bf j) * t ^ 2 := by ring

end QuantitativeCollapse
end OneSidedMFRadical
end Manuscript
end GroupApproximation
