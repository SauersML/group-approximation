import GroupApproximation.Higman.OmegaTowerSelectedLeadingCodeRun

/-!
# The selected nonzero-letter length induction

The binary normal form has one baseline code run and gains one syllable for
each nonzero selected letter.  This file packages the exact specialized
right-to-left induction.  The only local input is the suffix-growth statement
for a nonempty reduced tail; all singleton baselines are discharged here from
the concrete signed-factor formulas.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq
open GroupApproximation.Higman.Conj (F₃)
open Monoid Monoid.CoprodI
open BinarySyllableNormalizer

@[simp] theorem selectedSyllableList_nil (m : ℕ) {B : Set E} :
    selectedSyllableList m ([] : List (SelectedBlock m B × Bool)) = [] := rfl

def selectedNonzeroCount {m : ℕ} {B : Set E}
    (L : List (SelectedBlock m B × Bool)) : ℕ :=
  (L.filter fun p => (p.1 : E) ≠ 0).length

@[simp] theorem selectedNonzeroCount_nil {m : ℕ} {B : Set E} :
    selectedNonzeroCount ([] : List (SelectedBlock m B × Bool)) = 0 := rfl

theorem selectedNonzeroCount_cons {m : ℕ} {B : Set E}
    (p : SelectedBlock m B × Bool)
    (L : List (SelectedBlock m B × Bool)) :
    selectedNonzeroCount (p :: L) =
      (if (p.1 : E) = 0 then 0 else 1) + selectedNonzeroCount L := by
  by_cases hp : (p.1 : E) = 0
  · simp [selectedNonzeroCount, hp]
  · simp [selectedNonzeroCount, hp, Nat.add_comm]

/-- The one remaining local obligation in the global length induction:
prepending a nonzero selected letter to a nonempty reduced suffix increases
normalized syllable length by at least one; a zero letter never decreases it.
The head-code and two seam lemmas are designed to prove exactly this finite
case split. -/
def SelectedNormalizeGrowth (m : ℕ) (B : Set E) : Prop :=
  ∀ (p : SelectedBlock m B × Bool)
    (L : List (SelectedBlock m B × Bool)),
    FreeGroup.IsReduced (p :: L) → L ≠ [] →
    (if (p.1 : E) = 0 then 0 else 1) +
        (normalize (selectedSyllableList m L)).length ≤
      (normalize (selectedSyllableList m (p :: L))).length

/-- The normalized head is the first negative nonzero row exactly in that
case; otherwise it is the value of the maximal initial selected code run. -/
theorem normalize_selectedSyllableList_head
    {m : ℕ} {B : Set E} (p : SelectedBlock m B × Bool)
    (L : List (SelectedBlock m B × Bool))
    (hred : FreeGroup.IsReduced (p :: L)) :
    (selectedStartsWithRow p ∧
        ∃ q, normalize (selectedSyllableList m (p :: L)) =
          .row (lowRowFactor m (elt (p.1 : E))) :: q) ∨
      (¬ selectedStartsWithRow p ∧
        ∃ q, normalize (selectedSyllableList m (p :: L)) =
          .code (selectedCodeRunValue (leadingSelectedCodeRun (p :: L))) :: q) := by
  rcases p with ⟨beta, s⟩
  cases L with
  | nil =>
      cases s with
      | false =>
          by_cases hbeta : (beta : E) = 0
          · right
            refine ⟨by simp [selectedStartsWithRow, hbeta], [] , ?_⟩
            have hcode := leadingSelectedCodeRun_value_ne_one hred (by
              simp [leadingSelectedCodeRun, selectedStartsWithRow, hbeta])
            simp_all [selectedSyllableList_cons_zero,
              BinarySyllableNormalizer.normalize, prepend,
              leadingSelectedCodeRun, selectedStartsWithRow,
              selectedCodeRunValue]
          · left
            refine ⟨by simp [selectedStartsWithRow, hbeta],
              [.code ((aElt (beta : E))⁻¹)], ?_⟩
            have hrow := lowRowFactor_elt_ne_one_of_ne_zero beta.property.2 hbeta
            have hcode := cons_leadingSelectedCodeRun_value_ne_one hred
            simp_all [selectedSyllableList_cons_neg_ne_zero,
              BinarySyllableNormalizer.normalize, prepend,
              selectedCodeRunValue, leadingSelectedCodeRun]
      | true =>
          right
          refine ⟨by simp [selectedStartsWithRow], ?_⟩
          by_cases hbeta : (beta : E) = 0
          · refine ⟨[], ?_⟩
            have hcode := leadingSelectedCodeRun_value_ne_one hred (by
              simp [leadingSelectedCodeRun, selectedStartsWithRow, hbeta])
            simp_all [selectedSyllableList_cons_zero,
              BinarySyllableNormalizer.normalize, prepend,
              leadingSelectedCodeRun, selectedStartsWithRow,
              selectedCodeRunValue]
          · refine ⟨[.row ((lowRowFactor m (elt (beta : E)))⁻¹)], ?_⟩
            have hrow := lowRowFactor_elt_ne_one_of_ne_zero beta.property.2 hbeta
            have hcode := leadingSelectedCodeRun_value_ne_one hred (by
              simp [leadingSelectedCodeRun, selectedStartsWithRow, hbeta])
            simp_all [selectedSyllableList_cons_pos_ne_zero,
              BinarySyllableNormalizer.normalize, prepend,
              leadingSelectedCodeRun, selectedStartsWithRow,
              selectedCodeRunValue]
  | cons r T =>
      have htail : FreeGroup.IsReduced (r :: T) := hred.tail
      have ih := normalize_selectedSyllableList_head r T htail
      rcases ih with ⟨hrStart, q, hq⟩ | ⟨hrStart, q, hq⟩
      · rcases r with ⟨gamma, rs⟩
        have hrs : rs = false := hrStart.1
        subst rs
        have hgamma : (gamma : E) ≠ 0 := hrStart.2
        cases s with
        | false =>
            by_cases hbeta : (beta : E) = 0
            · right
              refine ⟨by simp [selectedStartsWithRow, hbeta], ?_⟩
              refine ⟨.row (lowRowFactor m (elt (gamma : E))) :: q, ?_⟩
              have hcode := cons_leadingSelectedCodeRun_value_ne_one hred
              simp_all [selectedSyllableList_cons_zero, normalize_cons,
                prepend, leadingSelectedCodeRun, selectedStartsWithRow,
                selectedCodeRunValue]
            · left
              refine ⟨by simp [selectedStartsWithRow, hbeta], ?_⟩
              refine ⟨.code ((aElt (beta : E))⁻¹) ::
                .row (lowRowFactor m (elt (gamma : E))) :: q, ?_⟩
              have hrow := lowRowFactor_elt_ne_one_of_ne_zero beta.property.2 hbeta
              have hcode := cons_leadingSelectedCodeRun_value_ne_one hred
              simp_all [selectedSyllableList_cons_neg_ne_zero,
                normalize_cons, prepend, leadingSelectedCodeRun,
                selectedStartsWithRow, selectedCodeRunValue]
        | true =>
            right
            refine ⟨by simp [selectedStartsWithRow], ?_⟩
            by_cases hbeta : (beta : E) = 0
            · refine ⟨.row (lowRowFactor m (elt (gamma : E))) :: q, ?_⟩
              have hcode := cons_leadingSelectedCodeRun_value_ne_one hred
              simp_all [selectedSyllableList_cons_zero, normalize_cons,
                prepend, leadingSelectedCodeRun, selectedStartsWithRow,
                selectedCodeRunValue]
            · have hseam := row_seam_ne_one_of_reduced_pos_neg hred
              refine ⟨.row ((lowRowFactor m (elt (beta : E)))⁻¹ *
                  lowRowFactor m (elt (gamma : E))) :: q, ?_⟩
              have hcode := leadingSelectedCodeRun_value_ne_one hred (by
                simp [leadingSelectedCodeRun, selectedStartsWithRow, hbeta])
              simp_all [selectedSyllableList_cons_pos_ne_zero,
                normalize_cons, prepend, leadingSelectedCodeRun,
                selectedStartsWithRow, selectedCodeRunValue]
      · cases s with
        | false =>
            by_cases hbeta : (beta : E) = 0
            · right
              refine ⟨by simp [selectedStartsWithRow, hbeta], ?_⟩
              refine ⟨q, ?_⟩
              have hcode := cons_leadingSelectedCodeRun_value_ne_one hred
              simp_all [selectedSyllableList_cons_zero, normalize_cons,
                prepend, leadingSelectedCodeRun, selectedStartsWithRow,
                selectedCodeRunValue]
            · left
              refine ⟨by simp [selectedStartsWithRow, hbeta], ?_⟩
              refine ⟨.code ((aElt (beta : E))⁻¹ *
                  selectedCodeRunValue (leadingSelectedCodeRun (r :: T))) :: q, ?_⟩
              have hrow := lowRowFactor_elt_ne_one_of_ne_zero beta.property.2 hbeta
              have hcode := cons_leadingSelectedCodeRun_value_ne_one hred
              simp_all [selectedSyllableList_cons_neg_ne_zero,
                normalize_cons, prepend, leadingSelectedCodeRun,
                selectedStartsWithRow, selectedCodeRunValue]
        | true =>
            right
            refine ⟨by simp [selectedStartsWithRow], ?_⟩
            by_cases hbeta : (beta : E) = 0
            · refine ⟨q, ?_⟩
              have hcode := cons_leadingSelectedCodeRun_value_ne_one hred
              simp_all [selectedSyllableList_cons_zero, normalize_cons,
                prepend, leadingSelectedCodeRun, selectedStartsWithRow,
                selectedCodeRunValue]
            · refine ⟨.row ((lowRowFactor m (elt (beta : E)))⁻¹) ::
                .code (selectedCodeRunValue (leadingSelectedCodeRun (r :: T))) :: q, ?_⟩
              have hrow := lowRowFactor_elt_ne_one_of_ne_zero beta.property.2 hbeta
              have hcode := leadingSelectedCodeRun_value_ne_one hred (by
                simp [leadingSelectedCodeRun, selectedStartsWithRow, hbeta])
              simp_all [selectedSyllableList_cons_pos_ne_zero,
                normalize_cons, prepend, leadingSelectedCodeRun,
                selectedStartsWithRow, selectedCodeRunValue]
termination_by L.length

theorem selectedNormalizeGrowth (m : ℕ) (B : Set E) :
    SelectedNormalizeGrowth m B := by
  intro p L hred hL
  obtain ⟨r, T, rfl⟩ := List.exists_cons_of_ne_nil hL
  have htail : FreeGroup.IsReduced (r :: T) := hred.tail
  have hhead := normalize_selectedSyllableList_head r T htail
  rcases p with ⟨beta, s⟩
  rcases hhead with ⟨hrStart, q, hq⟩ | ⟨hrStart, q, hq⟩
  · rcases r with ⟨gamma, rs⟩
    have hrs : rs = false := hrStart.1
    subst rs
    have hgamma : (gamma : E) ≠ 0 := hrStart.2
    cases s with
    | false =>
        by_cases hbeta : (beta : E) = 0
        · have hcode := cons_leadingSelectedCodeRun_value_ne_one hred
          have hz : (aElt (beta : E))⁻¹ ≠ 1 := by
            simpa [leadingSelectedCodeRun, selectedStartsWithRow, hbeta,
              hgamma, selectedCodeRunValue] using hcode
          have hz' : Conj.a⁻¹ ≠ 1 := by
            simpa [hbeta] using hz
          have hlist := selectedSyllableList_cons_zero m beta
            ((gamma, false) :: T) hbeta false
          rw [hlist]
          simp only [List.cons_append, List.nil_append]
          rw [normalize_cons, hq]
          simp [-Split.elt_eq_eltOn_support, prepend, hz', hbeta]
        · have hrow := lowRowFactor_elt_ne_one_of_ne_zero beta.property.2 hbeta
          have hcode := cons_leadingSelectedCodeRun_value_ne_one hred
          have hz : (aElt (beta : E))⁻¹ ≠ 1 := by
            simpa [leadingSelectedCodeRun, selectedStartsWithRow, hgamma,
              selectedCodeRunValue] using hcode
          have hlist := selectedSyllableList_cons_neg_ne_zero m beta
            ((gamma, false) :: T) hbeta
          rw [hlist]
          simp only [List.cons_append, List.nil_append]
          rw [normalize_cons, normalize_cons, hq]
          simp [-Split.elt_eq_eltOn_support, prepend, hrow, hz, hbeta]
          omega
    | true =>
        by_cases hbeta : (beta : E) = 0
        · have hcode := cons_leadingSelectedCodeRun_value_ne_one hred
          have hz : aElt (beta : E) ≠ 1 := by
            simpa [leadingSelectedCodeRun, selectedStartsWithRow, hbeta,
              hgamma, selectedCodeRunValue] using hcode
          have hz' : Conj.a ≠ 1 := by
            simpa [hbeta] using hz
          have hlist := selectedSyllableList_cons_zero m beta
            ((gamma, false) :: T) hbeta true
          rw [hlist]
          simp only [List.cons_append, List.nil_append]
          rw [normalize_cons, hq]
          simp [-Split.elt_eq_eltOn_support, prepend, hz', hbeta]
        · have hseam := row_seam_ne_one_of_reduced_pos_neg hred
          have hcode := leadingSelectedCodeRun_value_ne_one hred (by
            simp [leadingSelectedCodeRun, selectedStartsWithRow, hbeta])
          have hz : aElt (beta : E) ≠ 1 := by
            simpa [leadingSelectedCodeRun, selectedStartsWithRow, hbeta,
              selectedCodeRunValue] using hcode
          have hlist := selectedSyllableList_cons_pos_ne_zero m beta
            ((gamma, false) :: T) hbeta
          rw [hlist]
          simp only [List.cons_append, List.nil_append]
          rw [normalize_cons, normalize_cons, hq]
          simp [-Split.elt_eq_eltOn_support, prepend, hseam, hz, hbeta]
          omega
  · cases s with
    | false =>
        by_cases hbeta : (beta : E) = 0
        · have hcode := cons_leadingSelectedCodeRun_value_ne_one hred
          have hmerge : (aElt (beta : E))⁻¹ *
              selectedCodeRunValue (leadingSelectedCodeRun (r :: T)) ≠ 1 := by
            simpa [leadingSelectedCodeRun, selectedStartsWithRow, hbeta,
              selectedCodeRunValue] using hcode
          have hmerge' : Conj.a⁻¹ *
              selectedCodeRunValue (leadingSelectedCodeRun (r :: T)) ≠ 1 := by
            simpa [hbeta] using hmerge
          have hlist := selectedSyllableList_cons_zero m beta
            (r :: T) hbeta false
          rw [hlist]
          simp only [List.cons_append, List.nil_append]
          rw [normalize_cons, hq]
          simp [-Split.elt_eq_eltOn_support, prepend, hmerge', hbeta]
        · have hrow := lowRowFactor_elt_ne_one_of_ne_zero beta.property.2 hbeta
          have hcode := cons_leadingSelectedCodeRun_value_ne_one hred
          have hmerge : (aElt (beta : E))⁻¹ *
              selectedCodeRunValue (leadingSelectedCodeRun (r :: T)) ≠ 1 := by
            simpa [selectedCodeRunValue] using hcode
          have hlist := selectedSyllableList_cons_neg_ne_zero m beta
            (r :: T) hbeta
          rw [hlist]
          simp only [List.cons_append, List.nil_append]
          rw [normalize_cons, normalize_cons, hq]
          simp [-Split.elt_eq_eltOn_support, prepend, hrow, hmerge, hbeta]
          omega
    | true =>
        by_cases hbeta : (beta : E) = 0
        · have hcode := cons_leadingSelectedCodeRun_value_ne_one hred
          have hmerge : aElt (beta : E) *
              selectedCodeRunValue (leadingSelectedCodeRun (r :: T)) ≠ 1 := by
            simpa [leadingSelectedCodeRun, selectedStartsWithRow, hbeta,
              selectedCodeRunValue] using hcode
          have hmerge' : Conj.a *
              selectedCodeRunValue (leadingSelectedCodeRun (r :: T)) ≠ 1 := by
            simpa [hbeta] using hmerge
          have hlist := selectedSyllableList_cons_zero m beta
            (r :: T) hbeta true
          rw [hlist]
          simp only [List.cons_append, List.nil_append]
          rw [normalize_cons, hq]
          simp [-Split.elt_eq_eltOn_support, prepend, hmerge', hbeta]
        · have hrow := lowRowFactor_elt_ne_one_of_ne_zero beta.property.2 hbeta
          have hcode := leadingSelectedCodeRun_value_ne_one hred (by
            simp [leadingSelectedCodeRun, selectedStartsWithRow, hbeta])
          have hz : aElt (beta : E) ≠ 1 := by
            simpa [leadingSelectedCodeRun, selectedStartsWithRow, hbeta,
              selectedCodeRunValue] using hcode
          have hlist := selectedSyllableList_cons_pos_ne_zero m beta
            (r :: T) hbeta
          rw [hlist]
          simp only [List.cons_append, List.nil_append]
          rw [normalize_cons, normalize_cons, hq]
          simp [-Split.elt_eq_eltOn_support, prepend, hrow, hz, hbeta]
          omega

/-- A singleton zero letter has one normalized code syllable. -/
theorem normalize_selected_singleton_length_eq_one_of_zero
    {m : ℕ} {B : Set E} (p : SelectedBlock m B × Bool)
    (hp : (p.1 : E) = 0) :
    (normalize (selectedSyllableList m [p])).length = 1 := by
  have hcode : selectedCodeRunValue [p] ≠ 1 := by
    rw [selectedCodeRunValue_eq_selectedAHom_mk]
    exact selectedAHom_mk_ne_one_of_isReduced FreeGroup.IsReduced.singleton
      (List.cons_ne_nil _ _)
  rcases p with ⟨beta, s⟩
  cases s with
  | false =>
      have hlist := selectedSyllableList_cons_zero m beta [] hp false
      rw [hlist]
      simp [selectedCodeRunValue] at hcode
      simp [BinarySyllableNormalizer.normalize, prepend, hcode]
  | true =>
      have hlist := selectedSyllableList_cons_zero m beta [] hp true
      rw [hlist]
      simp [selectedCodeRunValue] at hcode
      simp [BinarySyllableNormalizer.normalize, prepend, hcode]

/-- A singleton nonzero letter has its two advertised alternating syllables. -/
theorem normalize_selected_singleton_length_eq_two_of_ne_zero
    {m : ℕ} {B : Set E} (p : SelectedBlock m B × Bool)
    (hp : (p.1 : E) ≠ 0) :
    (normalize (selectedSyllableList m [p])).length = 2 := by
  have hcode : selectedCodeRunValue [p] ≠ 1 := by
    rw [selectedCodeRunValue_eq_selectedAHom_mk]
    exact selectedAHom_mk_ne_one_of_isReduced FreeGroup.IsReduced.singleton
      (List.cons_ne_nil _ _)
  have hrow : lowRowFactor m (elt (p.1 : E)) ≠ 1 :=
    lowRowFactor_elt_ne_one_of_ne_zero p.1.property.2 hp
  rcases p with ⟨beta, s⟩
  cases s with
  | false =>
      have hcodeBeta : aElt (beta : E) ≠ 1 := by
        simpa [selectedCodeRunValue] using hcode
      have hcodeInv : (aElt (beta : E))⁻¹ ≠ 1 := inv_ne_one.mpr hcodeBeta
      have hlist := selectedSyllableList_cons_neg_ne_zero m beta [] hp
      rw [hlist]
      simp only [selectedSyllableList_nil, List.append_nil]
      simp [-Split.elt_eq_eltOn_support, BinarySyllableNormalizer.normalize,
        prepend, hrow, hcodeInv]
  | true =>
      have hcodeBeta : aElt (beta : E) ≠ 1 := by
        simpa [selectedCodeRunValue] using hcode
      have hlist := selectedSyllableList_cons_pos_ne_zero m beta [] hp
      rw [hlist]
      simp only [selectedSyllableList_nil, List.append_nil]
      simp [-Split.elt_eq_eltOn_support, BinarySyllableNormalizer.normalize,
        prepend, hrow, hcodeBeta]

/-- The global lower bound follows from the specialized nonempty-tail growth
step and the concrete singleton baselines. -/
theorem selectedNonzeroCount_add_one_le_normalize_length_of_growth
    {m : ℕ} {B : Set E} (hgrowth : SelectedNormalizeGrowth m B) :
    ∀ {L : List (SelectedBlock m B × Bool)},
      FreeGroup.IsReduced L → L ≠ [] →
      selectedNonzeroCount L + 1 ≤
        (normalize (selectedSyllableList m L)).length := by
  intro L hred hne
  induction L with
  | nil => exact absurd rfl hne
  | cons p L ih =>
      cases L with
      | nil =>
          rw [selectedNonzeroCount_cons]
          by_cases hp : (p.1 : E) = 0
          · simp [hp, normalize_selected_singleton_length_eq_one_of_zero p hp]
          · simp [hp, normalize_selected_singleton_length_eq_two_of_ne_zero p hp]
      | cons q L =>
          have htail : FreeGroup.IsReduced (q :: L) := hred.tail
          have ih' := ih htail (List.cons_ne_nil _ _)
          rw [selectedNonzeroCount_cons]
          exact le_trans (Nat.add_le_add_left ih'
              (if (p.1 : E) = 0 then 0 else 1))
            (by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                hgrowth p (q :: L) hred (List.cons_ne_nil _ _))

theorem selectedNonzeroCount_add_one_le_normalize_length
    {m : ℕ} {B : Set E} {L : List (SelectedBlock m B × Bool)}
    (hred : FreeGroup.IsReduced L) (hne : L ≠ []) :
    selectedNonzeroCount L + 1 ≤
      (normalize (selectedSyllableList m L)).length :=
  selectedNonzeroCount_add_one_le_normalize_length_of_growth
    (selectedNormalizeGrowth m B) hred hne

/-- A returning three-syllable equation contains at most two nonzero selected
letters in its canonical reduced spelling. -/
theorem selectedNonzeroCount_toWord_le_two_of_indexed_equation
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)} {l f : E}
    (hEq : selectedIndexedLinkHom m B v =
      CoprodI.of (i := false) (lowRowFactor m (elt l)) *
        CoprodI.of (i := true) (selectedAHom m B v) *
          (CoprodI.of (i := false) (lowRowFactor m (elt f)))⁻¹) :
    selectedNonzeroCount v.toWord ≤ 2 := by
  by_cases hv : v.toWord = []
  · simp [hv, selectedNonzeroCount]
  · have hlower := selectedNonzeroCount_add_one_le_normalize_length
      FreeGroup.isReduced_toWord hv
    have hupper := selectedNormalizedWord_length_le_three_of_equation hEq
    rw [selectedNormalizedWord_toList, List.length_map] at hupper
    omega

end Omega
end Higman
end GroupApproximation
