import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Code.RelatorsFinite
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Code.RawConfig
import GroupApproximation.Computability.AdianRabinWordProblem
import GroupApproximation.Computability.PresentationCodeCompleteness
import Mathlib.Computability.Partrec
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# A presentation code for `G(M)` with a computable family of configuration words

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`, in the
form of the coding step for the Kharlampovich group `KMS.KhGroup M`.

Since the defining relators of `G(M)` form a finite set (`KMS.relators_finite`), the
letter numbering `KMS.genEquiv K N` turns `G(M)` into a group presented by a code. The
word `KMS.configCode K N s (α, β)` codes
`(configuration word of (s; α, β, 0, …, 0)) * (configuration word of (0; 0, …, 0))⁻¹`
(KMS Theorem `tmm`(b)). It depends computably on `(α, β)`, and it is trivial in the
coded group exactly when the two configuration elements of `G(M)` are equal.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

open PresentationCodes

/-- **`G(M)` has a presentation code, and equality of an input configuration element
with the stop configuration element is a computable family of word problem instances.** -/
theorem exists_code_wordProblem_iff {K N : ℕ} (M : Minsky.Machine K N) (s : Fin (N + 1)) :
    ∃ (c : PresentationCodes.PresentationCode) (_ : PresentationCodes.Carrier c ≃* KMS.KhGroup M)
      (w : ℕ × ℕ → List (ℕ × Bool)), Computable w ∧ ∀ p : ℕ × ℕ,
        (AdianRabinWordProblem.WordProblem c (w p) ↔
          KMS.configElem M ⟨s, Minsky.initGlasses K p.1 p.2⟩ =
            KMS.configElem M (Minsky.stopCfg K N)) := by
  have hfin : (FreeGroup.freeGroupCongr (genEquiv K N) '' relators M).Finite :=
    (relators_finite M).image (FreeGroup.freeGroupCongr (genEquiv K N))
  have hnorm : Subgroup.normalClosure
      ((relatorFinset (codeOf hfin.toFinset) :
          Finset (FreeGroup (Fin (genIndexCount K N + 1)))) :
        Set (FreeGroup (Fin (genIndexCount K N + 1)))) =
      Subgroup.normalClosure (FreeGroup.freeGroupCongr (genEquiv K N) '' relators M) := by
    rw [relatorFinset_codeOf, Set.Finite.coe_toFinset]
  obtain ⟨φ, hφ⟩ : ∃ φ : Carrier (codeOf hfin.toFinset) ≃* KhGroup M,
      ∀ L : List (ℕ × Bool),
        φ (PresentedGroup.mk (AdianRabinWordProblem.relatorSet (codeOf hfin.toFinset))
            (wordOf (codeOf hfin.toFinset) L)) =
          PresentedGroup.mk (relators M) (rawEval K N (hfin.toFinset.toList.map encodeWord) L) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hnorm).trans
      (PresentedGroup.equivPresentedGroup (relators M) (genEquiv K N)).symm, fun _ ↦ rfl⟩
  have hstop : configElem M (Minsky.stopCfg K N) =
      PresentedGroup.mk (relators M) (configWord (⟨0, fun _ ↦ 0⟩ : Minsky.Cfg K N)) :=
    rfl
  refine ⟨codeOf hfin.toFinset, φ, configCode K N s,
    (primrec_configCode (K := K) s).to_comp, fun p ↦ ?_⟩
  rw [AdianRabinWordProblem.WordProblem, ← MulEquiv.map_eq_one_iff φ, hφ, rawEval_configCode,
    hstop, configElem, map_mul, map_inv, mul_inv_eq_one]

end KMS

end GroupApproximation.Full.Kharlampovich
