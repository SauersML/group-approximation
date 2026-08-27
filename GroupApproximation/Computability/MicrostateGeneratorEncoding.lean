import GroupApproximation.Computability.EffectiveMicrostateSemantics
import GroupApproximation.Computability.MicrostateNaturalize
import GroupApproximation.Computability.RationalMatrixEncoding

/-!
# Encoding the generators of a naturalized microstate

After reindexing an analytic microstate onto `Fin (d + 1)`, each of its finitely
many generator unitaries can be approximated by an exactly-unitary executable
`MatrixCode`.  This file packages those choices into the precise list syntax
used by `EffectiveMatrixCode.generator`.

No word-perturbation estimate is asserted here.  The output boundary is the
finite generator packet, exact unitarity of every coded generator, and uniform
operator-norm closeness to the reindexed analytic generators.
-/

namespace GroupApproximation
namespace MicrostateGeneratorEncoding

open PresentationCodes EffectiveMatrixCode EffectiveMicrostateSemantics
open MFMicrostate
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

/-- Reindex a microstate onto the natural nonempty dimension `Fin (d + 1)` and
encode all its generators by exactly-unitary rational matrix codes. -/
theorem exists_generatorCodes_close {c : PresentationCode} (M : Microstate c)
    (d : ℕ) (e : M.model ≃ Fin (dim d)) {ε : ℝ} (hε : 0 < ε) :
    ∃ gens : List MatrixCode,
      GeneratorsUnitary c d gens ∧
      ∀ i : Fin (genCount c),
        ‖(((unitaryReindexEquiv e (M.gen i) :
            Matrix.unitaryGroup (Fin (dim d)) ℂ) :
              Matrix (Fin (dim d)) (Fin (dim d)) ℂ) -
            toMatrix d (generator d gens i))‖ < ε := by
  classical
  have hcode : ∀ i : Fin (genCount c), ∃ C : MatrixCode,
      isUnitary d C ∧
        ‖(((unitaryReindexEquiv e (M.gen i) :
            Matrix.unitaryGroup (Fin (dim d)) ℂ) :
            Matrix (Fin (dim d)) (Fin (dim d)) ℂ) - toMatrix d C)‖ < ε := by
    intro i
    exact RationalMatrixEncoding.exists_unitary_matrixCode_close d
      (unitaryReindexEquiv e (M.gen i)).2 hε
  choose C hCunitary hCclose using hcode
  let gens : List MatrixCode := List.ofFn C
  have hgenerator (i : Fin (genCount c)) : generator d gens i = C i := by
    rw [generator, List.getD_eq_getElem?_getD]
    change (List.ofFn C)[i.val]?.getD (identity d) = C i
    have hi : i.val < (List.ofFn C).length := by
      simpa only [List.length_ofFn, Fintype.card_fin] using i.isLt
    rw [List.getElem?_eq_getElem hi]
    simp only [List.getElem_ofFn, Option.getD_some]
  refine ⟨gens, ?_, ?_⟩
  · intro i
    rw [hgenerator]
    exact hCunitary i
  · intro i
    rw [hgenerator]
    exact hCclose i

/-- Every microstate admits the preceding encoding in its canonical natural
dimension `card - 1`; positivity of a microstate's model makes
`card = (card - 1) + 1`. -/
theorem exists_naturalized_generatorCodes_close {c : PresentationCode}
    (M : Microstate c) {ε : ℝ} (hε : 0 < ε) :
    let d := Fintype.card M.model - 1
    ∃ (e : M.model ≃ Fin (dim d)) (gens : List MatrixCode),
      GeneratorsUnitary c d gens ∧
      (∀ i : Fin (genCount c),
        ‖(((unitaryReindexEquiv e (M.gen i) :
            Matrix.unitaryGroup (Fin (dim d)) ℂ) :
              Matrix (Fin (dim d)) (Fin (dim d)) ℂ) -
            toMatrix d (generator d gens i))‖ < ε) ∧
      ∀ w : List (ℕ × Bool),
        (M.reindex (naturalFiniteModel (dim d)) e).len w = M.len w := by
  dsimp only
  let d := Fintype.card M.model - 1
  have hcard : Fintype.card M.model = dim d := by
    rw [dim]
    exact (Nat.sub_add_cancel (Nat.succ_le_iff.2 M.card_pos)).symm
  let e : M.model ≃ Fin (dim d) :=
    (Fintype.equivFin M.model).trans (finCongr hcard)
  obtain ⟨gens, hunitary, hclose⟩ :=
    exists_generatorCodes_close M d e hε
  exact ⟨e, gens, hunitary, hclose,
    fun w ↦ M.reindex_len (naturalFiniteModel (dim d)) e w⟩

end

end MicrostateGeneratorEncoding
end GroupApproximation
