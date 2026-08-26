import GroupApproximation.Computability.CodedMicrostateEncoding
import GroupApproximation.Computability.ArithmeticalHierarchy
import GroupApproximation.Computability.EffectiveMicrostateSemantics
import GroupApproximation.Computability.EffectiveOperatorNormCode
import GroupApproximation.Computability.MicrostateNaturalize
import GroupApproximation.Computability.MicrostateNormalForm
import GroupApproximation.Computability.RationalMatrixEncoding

/-!
# A `Π⁰₂` upper bound for Operator-MF recognition

Open microstate inequalities permit exact Gaussian-rational unitary
approximants.  Power/Frobenius certificates then replace both strict operator
norm comparisons by total Boolean tests.  Together with the executable word
problem search this gives a computable checker whose `∀∃` truth condition is
exactly Operator-MF for the repository's concrete finite-presentation codes.

This file proves the upper bound only.  It makes no hardness or completeness
claim.
-/

namespace GroupApproximation
namespace MFRecognitionPi02

open Nat.Partrec
open ArithmeticalHierarchy
open PresentationCodes AdianRabinWordProblem RawWord
open EffectiveMatrixCode EffectiveMatrixCodePrimrec
open EffectiveOperatorNormCode
open CodedMicrostateEncoding
open EffectiveMicrostateSemantics
open MFMicrostate
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

/-! ## Strict-open microstate normal form -/

/-- The open finite packet used by rational approximation. -/
def PassesOpen (c : PresentationCode) (W : List (List (ℕ × Bool))) (k : ℕ)
    (M : Microstate c) : Prop :=
  (∀ r ∈ c.2, M.len r < 1 / ((k : ℝ) + 1)) ∧
    (∀ w ∈ W, 1 / 3 < M.len w)

/-- An open challenge is void or has an open-packet microstate. -/
def AnswersOpen (c : PresentationCode) (W : List (List (ℕ × Bool)))
    (k : ℕ) : Prop :=
  (∃ w ∈ W, WordProblem c w) ∨ ∃ M : Microstate c, PassesOpen c W k M

private theorem finer_scale_lt (k : ℕ) :
    1 / ((((2 * k + 1 : ℕ) : ℝ)) + 1) < 1 / ((k : ℝ) + 1) := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hrewrite : ((((2 * k + 1 : ℕ) : ℝ)) + 1) =
      2 * ((k : ℝ) + 1) := by push_cast; ring
  rw [hrewrite]
  calc
    1 / (2 * ((k : ℝ) + 1)) = (1 / 2 : ℝ) * (1 / ((k : ℝ) + 1)) := by
      field_simp
    _ < 1 * (1 / ((k : ℝ) + 1)) :=
      mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ = 1 / ((k : ℝ) + 1) := one_mul _

/-- Operator-MF is exactly the assertion that every strict-open challenge is
answered.  The forward direction creates slack by querying the closed normal
form at scale `2*k+1`; the backward direction uses the same area argument with
fixed separation `1/3`. -/
theorem isOperatorMF_iff_forall_openAnswers (c : PresentationCode) :
    IsOperatorMF (Carrier c) ↔ ∀ W k, AnswersOpen c W k := by
  classical
  constructor
  · intro hMF W k
    rcases (MFMicrostate.isOperatorMF_iff_forall_answers c).1 hMF W (2 * k + 1) with
      hvoid | ⟨M, hrel, hsep⟩
    · exact Or.inl hvoid
    · refine Or.inr ⟨M, ?_, ?_⟩
      · intro r hr
        exact (hrel r hr).trans_lt (finer_scale_lt k)
      · intro w hw
        have := hsep w hw
        linarith
  · intro h
    refine (show IsWeakMF (Carrier c) from ⟨1 / 3, by norm_num, ?_⟩).isOperatorMF
    intro F ε hε
    set wd : Carrier c → List (ℕ × Bool) := Function.surjInv (ev_surjective c)
      with hwd
    have hwdspec : ∀ g : Carrier c, ev c (wd g) = g := fun g ↦
      Function.surjInv_eq (ev_surjective c) g
    set pairs : Finset (Carrier c × Carrier c) :=
      (F ×ˢ F).filter fun q ↦ q.1 ≠ q.2 with hpairs
    set W : List (List (ℕ × Bool)) :=
      pairs.toList.map fun q ↦ invWord (wd q.1) ++ wd q.2 with hW
    set mulWords : List (List (ℕ × Bool)) :=
      (F ×ˢ F).toList.map fun q ↦
        invWord (wd q.1 ++ wd q.2) ++ wd (q.1 * q.2) with hmul
    have hmultriv : ∀ u ∈ mulWords, WordProblem c u := by
      intro u hu
      rw [hmul, List.mem_map] at hu
      obtain ⟨q, _hq, rfl⟩ := hu
      rw [← ev_eq_one_iff, ev_append, ev_invWord, ev_append, hwdspec,
        hwdspec, hwdspec, inv_mul_cancel]
    obtain ⟨N, hN⟩ := exists_area_bound_list c mulWords hmultriv
    obtain ⟨k, hk⟩ := exists_nat_gt ((N : ℝ) / ε)
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hNk : (N : ℝ) * (1 / ((k : ℝ) + 1)) ≤ ε := by
      have h1 : (N : ℝ) / ε < (k : ℝ) + 1 := by linarith
      have h2 : (N : ℝ) < ε * ((k : ℝ) + 1) := by
        have := (div_lt_iff₀ hε).1 h1
        linarith
      rw [mul_one_div]
      exact (div_le_iff₀ hkpos).2 (by linarith)
    rcases h W k with hvoid | ⟨M, hrel, hsep⟩
    · exfalso
      obtain ⟨w, hw, hwtriv⟩ := hvoid
      rw [hW, List.mem_map] at hw
      obtain ⟨q, hq, rfl⟩ := hw
      rw [Finset.mem_toList, hpairs, Finset.mem_filter] at hq
      rw [← ev_eq_one_iff, ev_append, ev_invWord, hwdspec, hwdspec,
        inv_mul_eq_one] at hwtriv
      exact hq.2 hwtriv
    refine ⟨{
      carrier := M.model
      nonempty := M.card_pos
      map := fun g ↦ ((M.hom (wordOf c (wd g)) :
        Matrix.unitaryGroup M.model ℂ) : Matrix M.model M.model ℂ)
      isUnitary := fun g ↦ (M.hom (wordOf c (wd g))).2
      multiplicative := ?_
      separated := ?_ }⟩
    · intro g hg h' hh'
      have hmemword :
          (invWord (wd g ++ wd h') ++ wd (g * h')) ∈ mulWords := by
        rw [hmul, List.mem_map]
        refine ⟨(g, h'), ?_, rfl⟩
        rw [Finset.mem_toList, Finset.mem_product]
        exact ⟨hg, hh'⟩
      have hval : M.len (invWord (wd g ++ wd h') ++ wd (g * h')) =
          opLength M.model
            ((M.hom (wordOf c (wd g)) * M.hom (wordOf c (wd h')))⁻¹ *
              M.hom (wordOf c (wd (g * h')))) := by
        rw [Microstate.len_def, wordOf_append, wordOf_invWord, wordOf_append,
          map_mul, map_inv, map_mul]
      have hbound := hN M (1 / ((k : ℝ) + 1)) (by positivity)
        (fun r hr ↦ (hrel r hr).le) _ hmemword
      rw [hval] at hbound
      have hfinal := hbound.trans hNk
      rw [opLength_inv_mul] at hfinal
      simpa using hfinal
    · intro g hg h' hh' hne
      have hmemword : (invWord (wd h') ++ wd g) ∈ W := by
        rw [hW, List.mem_map]
        refine ⟨(h', g), ?_, rfl⟩
        rw [Finset.mem_toList, hpairs, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hh', hg⟩, Ne.symm hne⟩
      have hval : M.len (invWord (wd h') ++ wd g) =
          opLength M.model
            ((M.hom (wordOf c (wd h')))⁻¹ * M.hom (wordOf c (wd g))) := by
        rw [Microstate.len_def, wordOf_append, wordOf_invWord, map_mul, map_inv]
      have hbound := (hsep _ hmemword).le
      rw [hval, opLength_inv_mul] at hbound
      simpa using hbound

/-! ## Finite-word perturbation and rationalization -/

private theorem norm_inv_sub_inv_unitary {Y : FiniteModel}
    (u v : Matrix.unitaryGroup Y ℂ) :
    ‖((u⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) -
        ((v⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)‖ =
      ‖(u : Matrix Y Y ℂ) - (v : Matrix Y Y ℂ)‖ := by
  have hu : (((u⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)) =
      (u : Matrix Y Y ℂ)ᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    rfl
  have hv : (((v⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)) =
      (v : Matrix Y Y ℂ)ᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    rfl
  rw [hu, hv]
  have hsub : (u : Matrix Y Y ℂ)ᴴ - (v : Matrix Y Y ℂ)ᴴ =
      ((u : Matrix Y Y ℂ) - (v : Matrix Y Y ℂ))ᴴ := by simp
  rw [hsub, ← Matrix.star_eq_conjTranspose, norm_star]

private theorem norm_mul_sub_mul_unitary_le {Y : FiniteModel}
    (a b c d : Matrix.unitaryGroup Y ℂ) :
    ‖(a : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
        (b : Matrix Y Y ℂ) * (d : Matrix Y Y ℂ)‖ ≤
      ‖(a : Matrix Y Y ℂ) - (b : Matrix Y Y ℂ)‖ +
        ‖(c : Matrix Y Y ℂ) - (d : Matrix Y Y ℂ)‖ := by
  have h1 : ‖(a : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
      (b : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ)‖ =
      ‖(a : Matrix Y Y ℂ) - (b : Matrix Y Y ℂ)‖ := by
    rw [← Matrix.sub_mul, CStarRing.norm_mul_mem_unitary _ c.2]
  have h2 : ‖(b : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
      (b : Matrix Y Y ℂ) * (d : Matrix Y Y ℂ)‖ =
      ‖(c : Matrix Y Y ℂ) - (d : Matrix Y Y ℂ)‖ := by
    rw [← Matrix.mul_sub, CStarRing.norm_mem_unitary_mul _ b.2]
  calc
    ‖(a : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
        (b : Matrix Y Y ℂ) * (d : Matrix Y Y ℂ)‖ =
        ‖((a : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
            (b : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ)) +
          ((b : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
            (b : Matrix Y Y ℂ) * (d : Matrix Y Y ℂ))‖ := by
      rw [sub_add_sub_cancel]
    _ ≤
        ‖(a : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
            (b : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ)‖ +
          ‖(b : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
            (b : Matrix Y Y ℂ) * (d : Matrix Y Y ℂ)‖ :=
      norm_add_le _ _
    _ = _ := by rw [h1, h2]


end
end MFRecognitionPi02
end GroupApproximation
