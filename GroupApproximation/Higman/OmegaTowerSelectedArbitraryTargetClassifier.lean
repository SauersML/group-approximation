import GroupApproximation.Higman.OmegaTowerSelectedAbstractEndpointFactors
import GroupApproximation.Higman.OmegaTowerSelectedAtMostTwo
import GroupApproximation.Higman.OmegaTowerSelectedRowWord
import GroupApproximation.Higman.OmegaTowerLowRowTailDecomposition
import GroupApproximation.Higman.OmegaTowerCanonicalReturnRelation
import GroupApproximation.Higman.OmegaTowerSelectedArbitraryReturnWitness

/-!
# Canonicalizing an arbitrary returning row index

The orbit alphabet is intersected with the full row-label range, so its target
index is initially an arbitrary element of `K`.  The low-row/free-code normal
form and the intrinsic `K` equation together force that target to be `bK f`
for a canonical sequence `f`, with one of the four return relations.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open BinarySyllableNormalizer

theorem selectedNonzeroCount_toWord_le_two_of_factor_equation
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)}
    {left right : FreeGroup (LowIndex m)}
    (hEq : selectedIndexedLinkHom m B v =
      CoprodI.of (i := false) left *
        CoprodI.of (i := true) (selectedAHom m B v) *
          (CoprodI.of (i := false) right)⁻¹) :
    selectedNonzeroCount v.toWord ≤ 2 := by
  by_cases hv : v.toWord = []
  · simp [hv, selectedNonzeroCount]
  · have hlower := selectedNonzeroCount_add_one_le_normalize_length
      FreeGroup.isReduced_toWord hv
    have hnorm := normalize_selected_eq_factors hEq
    have hupper : (normalize (selectedSyllableList m v.toWord)).length ≤ 3 := by
      rw [hnorm]
      exact le_trans (length_normalize_le _) (by simp)
    omega

theorem endpointFactors_ne_one_of_nonzero_pair
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)}
    {left right : FreeGroup (LowIndex m)}
    {p q : SelectedBlock m B × Bool}
    (hpair : selectedNonzeroLetters v.toWord = [p, q])
    (hEq : selectedIndexedLinkHom m B v =
      CoprodI.of (i := false) left *
        CoprodI.of (i := true) (selectedAHom m B v) *
          (CoprodI.of (i := false) right)⁻¹) :
    left ≠ 1 ∧ right ≠ 1 := by
  have hv : v.toWord ≠ [] := by
    intro hv
    simp [hv, selectedNonzeroLetters] at hpair
  have hcount : selectedNonzeroCount v.toWord = 2 := by
    rw [selectedNonzeroCount_eq_length_nonzeroLetters, hpair]
    rfl
  have hlower := selectedNonzeroCount_add_one_le_normalize_length
    FreeGroup.isReduced_toWord hv
  rw [hcount] at hlower
  have hnorm := normalize_selected_eq_factors hEq
  have hcode : selectedAHom m B v ≠ 1 :=
    selectedAHom_ne_one_of_toWord_ne_nil hv
  constructor
  · intro hleft
    have hlen := congrArg List.length hnorm
    by_cases hright : right = 1 <;>
      simp [normalize, prepend, hleft, hright, hcode] at hlen
    all_goals omega
  · intro hright
    have hlen := congrArg List.length hnorm
    by_cases hleft : left = 1 <;>
      simp [normalize, prepend, hleft, hright, hcode] at hlen
    all_goals omega

theorem target_eq_add_of_selectedRowLetter_pos
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)}
    {l : E} {q : ↥Conj.K} (beta : SelectedBlock m B)
    (hv : selectedRowInvHom m B v = selectedRowLetter (beta, true))
    (hlTail : rightTailSet m l)
    (hRow : selectedRowInvHom m B v = bK l * q⁻¹) :
    q = bK ((beta : E) + l) := by
  have hratio : (bK (beta : E))⁻¹ = bK l * q⁻¹ := by
    simpa [selectedRowLetter] using hv.symm.trans hRow
  calc
    q = (bK l * q⁻¹)⁻¹ * bK l := by group
    _ = ((bK (beta : E))⁻¹)⁻¹ * bK l := by rw [← hratio]
    _ = bK (beta : E) * bK l := by group
    _ = bK ((beta : E) + l) :=
      (bK_add_rightTail beta.property.2 hlTail).symm

theorem target_eq_tail_of_selectedRowLetter_neg
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)}
    {l t : E} {q : ↥Conj.K} (beta : SelectedBlock m B)
    (hv : selectedRowInvHom m B v = selectedRowLetter (beta, false))
    (htTail : rightTailSet m t) (hlt : l = (beta : E) + t)
    (hRow : selectedRowInvHom m B v = bK l * q⁻¹) :
    q = bK t := by
  have hratio : bK (beta : E) = bK l * q⁻¹ := by
    simpa [selectedRowLetter] using hv.symm.trans hRow
  have hratio' : bK (beta : E) =
      (bK (beta : E) * bK t) * q⁻¹ := by
    simpa [hlt, bK_add_rightTail beta.property.2 htTail] using hratio
  have hcancel : (1 : ↥Conj.K) = bK t * q⁻¹ := by
    exact mul_left_cancel (show
      bK (beta : E) * 1 = bK (beta : E) * (bK t * q⁻¹) by
        simpa [mul_assoc] using hratio')
  exact (mul_inv_eq_one.mp hcancel.symm).symm

theorem target_eq_add_of_selectedRowLetter_pair
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)}
    {l t : E} {q : ↥Conj.K} (beta gamma : SelectedBlock m B)
    (hv : selectedRowInvHom m B v =
      selectedRowLetter (beta, false) * selectedRowLetter (gamma, true))
    (htTail : rightTailSet m t) (hlt : l = (beta : E) + t)
    (hRow : selectedRowInvHom m B v = bK l * q⁻¹) :
    q = bK ((gamma : E) + t) := by
  have hratio : bK (beta : E) * (bK (gamma : E))⁻¹ =
      bK l * q⁻¹ := by
    simpa [selectedRowLetter] using hv.symm.trans hRow
  have hratio' : bK (beta : E) * (bK (gamma : E))⁻¹ =
      (bK (beta : E) * bK t) * q⁻¹ := by
    simpa [hlt, bK_add_rightTail beta.property.2 htTail] using hratio
  have hcancel : (bK (gamma : E))⁻¹ = bK t * q⁻¹ := by
    exact mul_left_cancel (by simpa [mul_assoc] using hratio')
  calc
    q = (bK t * q⁻¹)⁻¹ * bK t := by group
    _ = ((bK (gamma : E))⁻¹)⁻¹ * bK t := by rw [← hcancel]
    _ = bK (gamma : E) * bK t := by group
    _ = bK ((gamma : E) + t) :=
      (bK_add_rightTail gamma.property.2 htTail).symm

/-- An arbitrary returning `K` index is a canonical sequence index, and the
source and target sequences satisfy the corrected four-case relation. -/
theorem exists_canonical_target_of_selected_equations
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)}
    {l : E} {q : ↥Conj.K} {right : FreeGroup (LowIndex m)}
    (hEq : selectedIndexedLinkHom m B v =
      CoprodI.of (i := false) (lowRowFactor m (elt l)) *
        CoprodI.of (i := true) (selectedAHom m B v) *
          (CoprodI.of (i := false) right)⁻¹)
    (hRow : selectedRowInvHom m B v = bK l * q⁻¹) :
    ∃ f : E, q = bK f ∧ CanonicalReturnRelation m B l f := by
  rcases selectedNonzeroLetters_cases_of_count_le_two
      (selectedNonzeroCount_toWord_le_two_of_factor_equation hEq) with
      hzero | ⟨p, hp⟩ | ⟨p, r, hpq⟩
  · have hall := selectedNonzeroLetters_eq_nil_iff_allZero.mp hzero
    have hvalue := selectedRowInvHom_eq_one_of_toWord_allZero hall
    have hratio : (1 : ↥Conj.K) = bK l * q⁻¹ := hvalue.symm.trans hRow
    have hq : q = bK l := by
      exact (mul_inv_eq_one.mp hratio.symm).symm
    exact ⟨l, hq, Or.inl rfl⟩
  · obtain ⟨Z₁, Z₂, hv, hZ₁, hZ₂⟩ :=
      decompose_of_selectedNonzeroLetters_eq_singleton hp
    have hvalue := selectedRowInvHom_eq_letter_of_decomposition hv hZ₁ hZ₂
    rcases p with ⟨beta, s⟩
    cases s with
    | true =>
        have hleft : lowRowFactor m (elt l) = 1 := by
          by_contra hne
          by_cases hZ₁nil : Z₁ = []
          · subst Z₁
            have hvHead : v.toWord = (beta, true) :: Z₂ := by simpa using hv
            have hstart :=
              (selectedStartsWithRow_iff_leftFactor_ne_one hvHead hEq).mpr hne
            exact (by simpa [selectedStartsWithRow] using hstart)
          · obtain ⟨z, Z, rfl⟩ := List.exists_cons_of_ne_nil hZ₁nil
            have hz : (z.1 : E) = 0 := hZ₁ z (by simp)
            have hvHead : v.toWord = z :: (Z ++ (beta, true) :: Z₂) := by
              simpa using hv
            have hstart :=
              (selectedStartsWithRow_iff_leftFactor_ne_one hvHead hEq).mpr hne
            exact (by simpa [selectedStartsWithRow, hz] using hstart)
        have hlTail :=
          (lowRowFactor_elt_eq_one_iff_rightTailSet m l).mp hleft
        let f : E := (beta : E) + l
        have hq : q = bK f :=
          target_eq_add_of_selectedRowLetter_pos beta hvalue hlTail hRow
        exact ⟨f, hq, Or.inr (Or.inl
          ⟨(beta : E), beta.property, hlTail, rfl⟩)⟩
    | false =>
        have hright : right = 1 := by
          by_contra hne
          by_cases hZ₂nil : Z₂ = []
          · subst Z₂
            have hvLast : v.toWord = Z₁ ++ [(beta, false)] := by simpa using hv
            have hend :=
              (selectedEndsWithRow_iff_rightFactor_ne_one hvLast hEq).mpr hne
            exact (by simpa [selectedEndsWithRow] using hend)
          · obtain ⟨Z, z, rfl⟩ := List.exists_append_cons_of_ne_nil hZ₂nil
            have hz : (z.1 : E) = 0 := hZ₂ z (by simp)
            have hvLast : v.toWord =
                (Z₁ ++ (beta, false) :: Z) ++ [z] := by
              simpa [List.append_assoc] using hv
            have hend :=
              (selectedEndsWithRow_iff_rightFactor_ne_one hvLast hEq).mpr hne
            exact (by simpa [selectedEndsWithRow, hz] using hend)
        have hleft : lowRowFactor m (elt l) ≠ 1 := by
          intro hleft
          have hnorm := normalize_selected_eq_factors hEq
          have hcode : selectedAHom m B v ≠ 1 :=
            selectedAHom_ne_one_of_toWord_ne_nil (by rw [hv]; simp)
          have hlower := selectedNonzeroCount_add_one_le_normalize_length
            FreeGroup.isReduced_toWord (by rw [hv]; simp)
          have hcount : selectedNonzeroCount v.toWord = 1 := by
            rw [selectedNonzeroCount_eq_length_nonzeroLetters, hp]
            rfl
          rw [hcount] at hlower
          have hlen := congrArg List.length hnorm
          simp [normalize, prepend, hleft, hright, hcode] at hlen
          omega
        have hZ₁nil : Z₁ = [] := by
          by_contra hne
          obtain ⟨z, Z, rfl⟩ := List.exists_cons_of_ne_nil hne
          have hz : (z.1 : E) = 0 := hZ₁ z (by simp)
          have hvHead : v.toWord = z :: (Z ++ (beta, false) :: Z₂) := by
            simpa using hv
          have hstart :=
            (selectedStartsWithRow_iff_leftFactor_ne_one hvHead hEq).mpr hleft
          exact (by simpa [selectedStartsWithRow, hz] using hstart)
        subst Z₁
        have hvHead : v.toWord = (beta, false) :: Z₂ := by simpa using hv
        have hstart : selectedStartsWithRow (beta, false) :=
          (selectedStartsWithRow_iff_leftFactor_ne_one hvHead hEq).mpr hleft
        have hbetaLow := lowRowFactor_eq_leftFactor_of_selectedStartsWithRow
          hvHead hEq hstart
        obtain ⟨t, htTail, hlt⟩ :=
          exists_rightTail_add_of_lowRowFactor_eq hbetaLow.symm
        have hq : q = bK t :=
          target_eq_tail_of_selectedRowLetter_neg beta hvalue htTail hlt hRow
        exact ⟨t, hq, Or.inr (Or.inr (Or.inl
          ⟨(beta : E), beta.property, htTail, hlt⟩))⟩
  · obtain ⟨Z₀, Z₁, Z₂, hv, hZ₀, hZ₁, hZ₂⟩ :=
      decompose_of_selectedNonzeroLetters_eq_pair hpq
    have hends := endpointFactors_ne_one_of_nonzero_pair hpq hEq
    have hZ₀nil : Z₀ = [] := by
      by_contra hne
      obtain ⟨z, Z, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hz : (z.1 : E) = 0 := hZ₀ z (by simp)
      have hvHead : v.toWord = z :: (Z ++ p :: (Z₁ ++ r :: Z₂)) := by
        simpa using hv
      have hstart :=
        (selectedStartsWithRow_iff_leftFactor_ne_one hvHead hEq).mpr hends.1
      exact (by simpa [selectedStartsWithRow, hz] using hstart)
    have hZ₂nil : Z₂ = [] := by
      by_contra hne
      obtain ⟨Z, z, rfl⟩ := List.exists_append_cons_of_ne_nil hne
      have hz : (z.1 : E) = 0 := hZ₂ z (by simp)
      have hvLast : v.toWord =
          (Z₀ ++ p :: (Z₁ ++ r :: Z)) ++ [z] := by
        simpa [List.append_assoc] using hv
      have hend :=
        (selectedEndsWithRow_iff_rightFactor_ne_one hvLast hEq).mpr hends.2
      exact (by simpa [selectedEndsWithRow, hz] using hend)
    subst Z₀
    subst Z₂
    have hvHead : v.toWord = p :: (Z₁ ++ [r]) := by simpa using hv
    have hpStart : selectedStartsWithRow p :=
      (selectedStartsWithRow_iff_leftFactor_ne_one hvHead hEq).mpr hends.1
    have hvLast : v.toWord = (p :: Z₁) ++ [r] := by
      simpa [List.append_assoc] using hvHead
    have hrEnd : selectedEndsWithRow r :=
      (selectedEndsWithRow_iff_rightFactor_ne_one hvLast hEq).mpr hends.2
    rcases p with ⟨beta, ps⟩
    rcases r with ⟨gamma, rs⟩
    have hps : ps = false := hpStart.1
    have hrs : rs = true := hrEnd.1
    subst ps
    subst rs
    have hbetaLow := lowRowFactor_eq_leftFactor_of_selectedStartsWithRow
      hvHead hEq hpStart
    obtain ⟨t, htTail, hlt⟩ :=
      exists_rightTail_add_of_lowRowFactor_eq hbetaLow.symm
    have hvalue := selectedRowInvHom_eq_mul_of_pair_decomposition
      (by simpa using hv) hZ₀ hZ₁ hZ₂
    have hq : q = bK ((gamma : E) + t) :=
      target_eq_add_of_selectedRowLetter_pair beta gamma hvalue htTail hlt hRow
    exact ⟨(gamma : E) + t, hq, Or.inr (Or.inr (Or.inr
      ⟨(beta : E), (gamma : E), t, beta.property, gamma.property,
        htTail, hlt, rfl⟩))⟩

theorem exists_canonical_target_of_selected_rightLabel_return
    {m : ℕ} {B : Set E} {g : Cent3 (rowOut m)} {l : E} {q : ↥Conj.K}
    (hg : g ∈ slimGenSub m B)
    (hlabel : CentralHNNFreeLabel.rightLabel
        (M := slimLink m) (slimTransversal m) g
          (slimRowLabel m (bK l)) = slimRowLabel m q) :
    ∃ f : E, q = bK f ∧ CanonicalReturnRelation m B l f := by
  obtain ⟨v, -, hEq, hRow⟩ :=
    exists_selected_arbitrary_indexed_return_witness hg hlabel
  exact exists_canonical_target_of_selected_equations hEq hRow

/-- An arbitrary row-label target of the selected orbit of an Omega label is
again a canonical Omega label. -/
theorem exists_omega_target_of_selected_rightLabel_return
    {m : ℕ} (hm : 0 < m) {B : Set E} (hzero : (0 : E) ∈ B)
    {g : Cent3 (rowOut m)} {l : E} {q : ↥Conj.K}
    (hl : l ∈ omegaOp m B) (hg : g ∈ slimGenSub m B)
    (hlabel : CentralHNNFreeLabel.rightLabel
        (M := slimLink m) (slimTransversal m) g
          (slimRowLabel m (bK l)) = slimRowLabel m q) :
    ∃ f ∈ omegaOp m B, q = bK f := by
  obtain ⟨f, hq, hreturn⟩ :=
    exists_canonical_target_of_selected_rightLabel_return hg hlabel
  exact ⟨f, omega_mem_of_canonicalReturnRelation hm hzero hl hreturn, hq⟩

end Omega
end Higman
end GroupApproximation
