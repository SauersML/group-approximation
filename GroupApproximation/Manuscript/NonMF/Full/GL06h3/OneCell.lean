import GroupApproximation.Manuscript.NonMF.Full.GL06h3.Statement
import GroupApproximation.Manuscript.NonMF.Full.GL06h2.Statement
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.GGT.HullSCRelatorFamily
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06h3: a short boundary around one relator cell

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the case of one cell.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).

A least-area diagram with exactly one relator cell `C` has boundary value the signed conjugate
`C.value`.  If `C` reads `1`, the boundary value is the empty relator product, against least area.
Otherwise the boundary word is a letter word conjugate to the value of `C.word` or of its formal
inverse, which lies in `W` as well; a short letter word conjugate to a nontrivial relator value is
excluded by the conclusion of `GL06h2.ShortWordNeConjRelatorStatement` for `W`.

* `boundaryWord_isLetter`: the boundary letters of a diagram with letter labels are letters.
* `false_of_oneCell`: the refutation, from the pointwise conclusion of GL06h2 for `W`.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06h3

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **Boundary letters are dart labels** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem boundaryWord_isLetter {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))}
    (Xi : DiscDiagram.{u, w, v} W)
    (hletters : ∀ d, (symmetricLabelAlphabet D).IsLetter (Xi.label d)) :
    ∀ x ∈ Xi.boundaryWord, (symmetricLabelAlphabet D).IsLetter x := by
  intro x hx
  rw [← Embedded.dartWord_outerDarts Xi] at hx
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp hx
  exact hletters d

/-- **A short boundary around one relator cell** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121).  A least-area diagram with one relator cell, letter labels and
boundary length at most `ε + ε` does not exist when no short letter word is conjugate to a
nontrivial relator value of `W`. -/
theorem false_of_oneCell {D : RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (hinv : ∀ v ∈ W, HullSC.RelWord.revInv v ∈ W)
    (hconj : ∀ word ∈ W, RelLetter.listVal word ≠ 1 →
      ∀ (g : G) (u : List (RelLetter G Lambda)),
        (∀ x ∈ u, (symmetricLabelAlphabet D).IsLetter x) →
        u.length ≤ eps + eps →
          RelLetter.listVal u ≠ g * RelLetter.listVal word * g⁻¹)
    (Xi : DiscDiagram.{u, w, v} W) (hlea : Xi.LeastArea)
    (hletters : ∀ d, (symmetricLabelAlphabet D).IsLetter (Xi.label d))
    (hone : Xi.rCellCount = 1) (hshort : Xi.boundaryWord.length ≤ eps + eps) : False := by
  have hlen : Xi.relatorCells.length = 1 := hone
  obtain ⟨C, hC⟩ := List.length_eq_one_iff.mp hlen
  have hval : Xi.boundaryValue = C.value := by
    rw [← Xi.relatorValues_prod_eq_boundaryValue, hC]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hb : ∀ x ∈ Xi.boundaryWord, (symmetricLabelAlphabet D).IsLetter x :=
    boundaryWord_isLetter Xi hletters
  have hbv : RelLetter.listVal Xi.boundaryWord = C.value := hval
  by_cases hw1 : RelLetter.listVal C.word = 1
  · have hv1 : Xi.boundaryValue = 1 := by
      rw [hval, RelatorCell.value]
      split <;> simp [hw1]
    have h0 : RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) 0 Xi.boundaryValue := by
      rw [hv1]
      exact RelatorDefectBudget.IsRelatorProduct.one
    have hzero : Xi.rCellCount ≤ 0 := hlea h0
    omega
  · cases hrev : C.reversed
    · have hv : C.value = C.conjugator * RelLetter.listVal C.word * C.conjugator⁻¹ := by
        have hf : ¬ C.reversed = true := by simp [hrev]
        rw [RelatorCell.value, if_neg hf]
      exact hconj C.word C.word_mem hw1 C.conjugator Xi.boundaryWord hb hshort (hbv.trans hv)
    · have hv : C.value = C.conjugator * RelLetter.listVal (HullSC.RelWord.revInv C.word) *
          C.conjugator⁻¹ := by
        rw [RelatorCell.value, if_pos hrev, HullSC.RelWord.listVal_revInv]
      have hw1' : RelLetter.listVal (HullSC.RelWord.revInv C.word) ≠ 1 := by
        rw [HullSC.RelWord.listVal_revInv]
        exact inv_ne_one.mpr hw1
      exact hconj _ (hinv C.word C.word_mem) hw1' C.conjugator Xi.boundaryWord hb hshort
        (hbv.trans hv)

end GroupApproximation.Full.GL06h3

#audit_axioms GroupApproximation.Full.GL06h3.boundaryWord_isLetter
#audit_axioms GroupApproximation.Full.GL06h3.false_of_oneCell
