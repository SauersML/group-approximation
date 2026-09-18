import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSubdiagramSuccAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Prep
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Manuscript.NonMF.Full.GL06h2.ShortConjugate
import GroupApproximation.Meta.AxiomGuard

/-!
# The all-cells short enclosed face set with one relator cell

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

In a least-area diagram `X` with exactly one relator cell and letter labels, an enclosed face set
(successor form) holding that cell cannot have an outside walk of length `≤ ε + ε`.  The enclosed
subdiagram `Ξ` (`closedWalkEnclosedSubdiagramSucc`) has least area and exactly one relator cell,
so its boundary word, a word of at most `ε + ε` letters of `X`, spells a signed conjugate of a
nontrivial relator value.  A reversed cell uses the formal inverse, which again lies in `W`.
`GL06h2.shortWord_ne_conj_relator` excludes this beyond its thresholds.

* `false_of_allCells_of_rCellCount_eq_one`: the refutation at fixed parameters.
* `allCellsShortEnclosed_refuted_of_rCellCount_eq_one`: the threshold form, with the hypothesis
  list of `GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement`, at relator count one.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06h

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded

/-- **An all-cells short enclosed face set with one relator cell does not exist** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  The enclosed subdiagram reads a short
letter word spelling a signed conjugate of a nontrivial relator value, which `hshort` excludes. -/
theorem false_of_allCells_of_rCellCount_eq_one
    {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps rho : ℕ} {W : Set (List (RelLetter G Lambda))}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hshort : ∀ word ∈ W, RelLetter.listVal word ≠ 1 →
      ∀ (g : G) (u : List (RelLetter G Lambda)),
        (∀ x ∈ u, (symmetricLabelAlphabet D).IsLetter x) →
        u.length ≤ eps + eps →
          RelLetter.listVal u ≠ g * RelLetter.listVal word * g⁻¹)
    {X : DiscDiagram.{u, w, v} W} (hlea : X.LeastArea)
    (hletters : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (hone : X.rCellCount = 1)
    {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart}
    (hE : EnclosedFaceSetSucc X faces outerWalk)
    (hall : ∀ C' ∈ X.relatorCells, C'.face ∈ faces)
    (hlen : outerWalk.length ≤ eps + eps) : False := by
  obtain ⟨Xi, hword, hcount, hposXi, -, hleaXi⟩ :=
    closedWalkEnclosedSubdiagramSucc.{u, w, v} X faces outerWalk hE
  have hpos : 0 < X.rCellCount := by
    rw [hone]
    exact Nat.one_pos
  have hcell : ∃ C ∈ X.relatorCells, C.face ∈ faces :=
    ⟨cell X ⟨0, hpos⟩, cell_mem X ⟨0, hpos⟩, hall _ (cell_mem X ⟨0, hpos⟩)⟩
  have hXi1 : Xi.relatorCells.length = 1 := by
    have h1 : Xi.rCellCount ≤ X.rCellCount := le_trans hcount (List.length_filter_le ..)
    have h2 : 0 < Xi.rCellCount := hposXi hcell
    have h3 : Xi.rCellCount = 1 := by omega
    exact h3
  have hu : ∀ x ∈ Xi.boundaryWord, (symmetricLabelAlphabet D).IsLetter x := by
    intro x hx
    rw [hword] at hx
    unfold dartWord at hx
    obtain ⟨d, -, hd⟩ := List.mem_map.mp hx
    rw [← hd]
    exact hletters d
  have hlenu : Xi.boundaryWord.length ≤ eps + eps := by
    rw [hword]
    unfold dartWord invDarts
    rw [List.length_map, List.length_map, List.length_reverse]
    exact hlen
  have hprod := Xi.relatorValues_prod_eq_boundaryValue
  rcases hcells : Xi.relatorCells with _ | ⟨C, _ | ⟨_, _⟩⟩
  · rw [hcells, List.length_nil] at hXi1
    omega
  · have hmem : C ∈ Xi.relatorCells := by
      rw [hcells]
      exact List.mem_singleton_self C
    have hne : RelLetter.listVal C.word ≠ 1 :=
      DiscDiagram.leastArea_listVal_word_ne_one (hleaXi hlea) C hmem
    rw [hcells] at hprod
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hprod
    have hval : RelLetter.listVal Xi.boundaryWord = C.value := hprod.symm
    unfold RelatorCell.value at hval
    cases hrev : C.reversed with
    | false =>
      have hf : ¬ (C.reversed = true) := by
        rw [hrev]
        decide
      rw [if_neg hf] at hval
      exact hshort C.word C.word_mem hne C.conjugator Xi.boundaryWord hu hlenu hval
    | true =>
      rw [if_pos hrev] at hval
      have hmemInv := hcondition.inv_mem C.word C.word_mem
      exact hshort _ hmemInv
        (by
          rw [HullSC.RelWord.listVal_revInv]
          exact inv_ne_one.mpr hne)
        C.conjugator Xi.boundaryWord hu hlenu
        (by
          rw [HullSC.RelWord.listVal_revInv]
          exact hval)
  · rw [hcells, List.length_cons, List.length_cons] at hXi1
    omega

/-- **The all-cells short enclosed face set with one relator cell, beyond thresholds** (Osin,
proof of Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  The hypothesis list and
thresholds of `GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement`, specialised to a diagram
with exactly one relator cell; the thresholds are those of `GL06h2.shortWord_ne_conj_relator`. -/
theorem allCellsShortEnclosed_refuted_of_rCellCount_eq_one
    {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda)
    (hD : ∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (lambda c mu : ℝ) (hlam : 0 < lambda) (hlam1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu)
    (hmu16 : mu ≤ 1 / 16) :
    ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
      ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
        ∀ (W : Set (List (RelLetter G Lambda))),
          OsinCCondition D W eps mu lambda c rho →
            ∀ X : DiscDiagram.{u, w, v} W, X.LeastArea →
              (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
              X.rCellCount = 1 →
              ∀ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
                EnclosedFaceSetSucc X faces outerWalk →
                (∀ C ∈ X.relatorCells, C.face ∈ faces) →
                outerWalk.length ≤ eps + eps →
                  False := by
  obtain ⟨eps0, h0⟩ := GL06h2.shortWord_ne_conj_relator D hD lambda c mu hlam hlam1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := h0 eps heps
  refine ⟨rho0, hrho0, fun rho hr W hcondition X hlea hletters hone faces outerWalk hE hall
    hlen => ?_⟩
  exact false_of_allCells_of_rCellCount_eq_one hcondition (hrho rho hr W hcondition) hlea hletters
    hone hE hall hlen

end GroupApproximation.Full.GL06h

#audit_axioms GroupApproximation.Full.GL06h.false_of_allCells_of_rCellCount_eq_one
#audit_axioms GroupApproximation.Full.GL06h.allCellsShortEnclosed_refuted_of_rCellCount_eq_one
