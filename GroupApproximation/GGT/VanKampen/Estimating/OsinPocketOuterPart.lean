import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixLeastAreaCut
import GroupApproximation.GGT.VanKampen.PlanarVanKampenDiagram
import GroupApproximation.Meta.AxiomGuard

/-!
# The outer part of a disc region

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The induction on the number of
`R`-cells applies clause (b) to the pocket `Γ_1` between the extreme contiguity subdiagrams,
so `Γ_1` must be least area when `Δ` is.  A shorter filling of the boundary word of the pocket,
put in place of the pocket, fills the boundary of `Δ` with fewer cells.

This file proves that exchange algebraically, for every disc region of every disc diagram.
Collapse the region into one new face (`Surgery.MapCollapse.replaceGRegion`).  The collapsed
map is planar, so the planar van Kampen lemma (`exists_relatorCells_of_planar`) writes its
boundary as a product of signed conjugates of its face words.  The new face contributes the
given filling of the boundary word of the region, a kept relator face one relator, and a kept
`G`-face nothing.

* `RelatorDefectBudget.isRelatorProduct_prod_map_sum`: budgets add along a list product.
* `RelatorCell.isRelatorProduct_value`: a cell value has the budget of its word.
* `Surgery.MapCollapse.replaceGRegionFaceBoundary_keptFace_word` and
  `Surgery.MapCollapse.replaceGRegionFaceBoundary_newFace_word`: the words of the faces of the
  collapse.
* `DiscDiagram.exists_isRelatorProduct_of_discRegion`: a filling of the boundary word of a
  disc region with `m` relators gives a filling of the boundary of `Δ` with at most `m` plus
  the number of relator cells outside the region.
* `DiscDiagram.LeastArea.length_filter_mem_le`: in a least-area diagram, a filling of the
  boundary word of a disc region needs at least as many relators as the region has relator
  cells.
-/

namespace GroupApproximation.RelatorDefectBudget

universe u

variable {G : Type u} [Group G]

/-- **Budgets add along a list product.**  If each entry `v x` is a relator product with
`b x` factors, the product of the entries is one with `∑ b x` factors. -/
theorem isRelatorProduct_prod_map_sum {R : Set G} {α : Type*} (b : α → ℕ) (v : α → G)
    (l : List α) (h : ∀ x ∈ l, IsRelatorProduct R (b x) (v x)) :
    IsRelatorProduct R (l.map b).sum (l.map v).prod := by
  induction l with
  | nil => simpa using (IsRelatorProduct.one : IsRelatorProduct R 0 1)
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    exact (h x (List.mem_cons.mpr (Or.inl rfl))).mul
      (ih fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))

end GroupApproximation.RelatorDefectBudget

namespace GroupApproximation.GGT.VanKampen

open HullSC Surgery.MapCollapse

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **A cell value has the budget of its word.** -/
theorem RelatorCell.isRelatorProduct_value {M : CombMap.{v}} {outer : M.Face}
    {W : Set (List (RelLetter G Lambda))} (C : RelatorCell M outer W) {R : Set G} {n : ℕ}
    (h : RelatorDefectBudget.IsRelatorProduct R n (RelLetter.listVal C.word)) :
    RelatorDefectBudget.IsRelatorProduct R n C.value := by
  unfold RelatorCell.value
  split
  · exact h.inv.conj C.conjugator
  · exact h.conj C.conjugator

namespace Surgery.MapCollapse

/-- A kept face of a collapse reads the word of its old face. -/
theorem replaceGRegionFaceBoundary_keptFace_word {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
    (region : IsDiscRegion Delta.toCombMap faces) (g : Delta.toCombMap.Face) (hg : g ∉ faces) :
    ((replaceGRegionFaceBoundary Delta.toCombMap faces region Delta.faceBoundary
        (keptFace Delta.toCombMap faces region g hg)).darts).map
      (fun d => Delta.label d.1) = Delta.faceWord g := by
  have hmap := replaceGRegionFaceBoundary_keptFace_map_val Delta.toCombMap faces region
    Delta.faceBoundary g hg
  calc ((replaceGRegionFaceBoundary Delta.toCombMap faces region Delta.faceBoundary
          (keptFace Delta.toCombMap faces region g hg)).darts).map (fun d => Delta.label d.1)
      = (((replaceGRegionFaceBoundary Delta.toCombMap faces region Delta.faceBoundary
            (keptFace Delta.toCombMap faces region g hg)).darts).map Subtype.val).map
          Delta.label := List.map_map.symm
    _ = ((Delta.faceBoundary g).darts).map Delta.label :=
        congrArg (fun l => l.map Delta.label) hmap
    _ = Delta.faceWord g := rfl

/-- The new face of a collapse reads the boundary cycle of the region. -/
theorem replaceGRegionFaceBoundary_newFace_word {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
    (region : IsDiscRegion Delta.toCombMap faces) :
    ((replaceGRegionFaceBoundary Delta.toCombMap faces region Delta.faceBoundary
        (newFace Delta.toCombMap faces region)).darts).map
      (fun d => Delta.label d.1) = Embedded.dartWord Delta region.toBoundaryCycle.cycle := by
  have hmap := replaceGRegionFaceBoundary_newFace_map_val Delta.toCombMap faces region
    Delta.faceBoundary
  calc ((replaceGRegionFaceBoundary Delta.toCombMap faces region Delta.faceBoundary
          (newFace Delta.toCombMap faces region)).darts).map (fun d => Delta.label d.1)
      = (((replaceGRegionFaceBoundary Delta.toCombMap faces region Delta.faceBoundary
            (newFace Delta.toCombMap faces region)).darts).map Subtype.val).map
          Delta.label := List.map_map.symm
    _ = (region.toBoundaryCycle.cycle).map Delta.label :=
        congrArg (fun l => l.map Delta.label) hmap
    _ = Embedded.dartWord Delta region.toBoundaryCycle.cycle := rfl

end Surgery.MapCollapse

open scoped Classical in
/-- **The outer part of a disc region.**  Let `faces` be a disc region of `Δ` away from the
exterior face.  If the boundary word of the region is a product of `m` signed conjugates of
relators, the boundary of `Δ` is a product of at most `m` plus the number of relator cells of
`Δ` outside the region.  Collapse the region into one face: the collapsed map is planar, and
its boundary is a product of signed conjugates of its face words, with `m` relators for the
new face, one for a kept relator face and none for a kept `G`-face. -/
theorem DiscDiagram.exists_isRelatorProduct_of_discRegion {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
    (region : IsDiscRegion Delta.toCombMap faces) (hout : Delta.outerFace ∉ faces) {m : ℕ}
    (hm : RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) m
      (RelLetter.listVal (Embedded.dartWord Delta region.toBoundaryCycle.cycle))) :
    ∃ n ≤ m + (Delta.relatorCells.filter (fun C => C.face ∉ faces)).length,
      RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) n Delta.boundaryValue := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (replaceGRegion Delta.toCombMap faces region).Face,
      S = ((Delta.relatorCells.filter (fun C => C.face ∉ faces)).map
        (fun C => if hC : C.face ∈ faces then newFace Delta.toCombMap faces region
          else keptFace Delta.toCombMap faces region C.face hC)).toFinset := ⟨_, rfl⟩
  obtain ⟨bf, hbf⟩ : ∃ bf : (replaceGRegion Delta.toCombMap faces region).Face → ℕ,
      bf = fun F => (if F = newFace Delta.toCombMap faces region then m else 0) +
        (if F ∈ S then 1 else 0) := ⟨_, rfl⟩
  -- The budget of each face word of the collapse.
  have hface : ∀ F : (replaceGRegion Delta.toCombMap faces region).Face,
      F ≠ keptFace Delta.toCombMap faces region Delta.outerFace hout →
        RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) (bf F)
          (RelLetter.listVal (((replaceGRegionFaceBoundary Delta.toCombMap faces region
            Delta.faceBoundary F).darts).map (fun d => Delta.label d.1))) := by
    intro F hF
    by_cases hnew : F = newFace Delta.toCombMap faces region
    · have hSn : F ∉ S := by
        rw [hS, List.mem_toFinset]
        intro hmem
        obtain ⟨C, hC, hCF⟩ := List.mem_map.mp hmem
        have hCout : C.face ∉ faces := by simpa using (List.mem_filter.mp hC).2
        simp only [dif_neg hCout] at hCF
        exact keptFace_ne_newFace Delta.toCombMap faces region C.face hCout (hCF.trans hnew)
      have hb : bf F = m := by simp only [hbf, if_pos hnew, if_neg hSn, Nat.add_zero]
      rw [hb]
      subst hnew
      rw [replaceGRegionFaceBoundary_newFace_word Delta faces region]
      exact hm
    · obtain ⟨g, hg, rfl⟩ := exists_keptFace_of_ne_newFace Delta.toCombMap faces region F hnew
      have hgo : g ≠ Delta.outerFace := fun h =>
        hF (keptFace_congr Delta.toCombMap faces region _ _ hg hout h)
      rw [replaceGRegionFaceBoundary_keptFace_word Delta faces region g hg]
      by_cases hSg : keptFace Delta.toCombMap faces region g hg ∈ S
      · have hb : bf (keptFace Delta.toCombMap faces region g hg) = 1 := by
          simp only [hbf, if_neg hnew, if_pos hSg, Nat.zero_add]
        rw [hb]
        rw [hS, List.mem_toFinset] at hSg
        obtain ⟨C, hC, hCF⟩ := List.mem_map.mp hSg
        have hC' := List.mem_filter.mp hC
        have hCout : C.face ∉ faces := by simpa using hC'.2
        simp only [dif_neg hCout] at hCF
        have hCg : C.face = g := keptFace_inj Delta.toCombMap faces region _ _ hCout hg hCF
        rw [← hCg, DiscDiagram.faceWord, ← Delta.relatorCell_word C hC'.1]
        exact RelatorDefectBudget.IsRelatorProduct.base ⟨C.word, C.word_mem, rfl⟩
      · have hb : bf (keptFace Delta.toCombMap faces region g hg) = 0 := by
          simp only [hbf, if_neg hnew, if_neg hSg, Nat.add_zero]
        rw [hb]
        rcases Delta.inner_face g hgo with ⟨C, hC, hCg⟩ | hone
        · exfalso
          apply hSg
          rw [hS, List.mem_toFinset]
          subst hCg
          exact List.mem_map.mpr ⟨C, List.mem_filter.mpr ⟨hC, by simpa using hg⟩, dif_neg hg⟩
        · rw [DiscDiagram.faceWord, hone]
          exact RelatorDefectBudget.IsRelatorProduct.one
  -- The total budget over any set of faces.
  have hbound : ∀ T : Finset (replaceGRegion Delta.toCombMap faces region).Face,
      T.sum bf ≤ m + S.card := by
    intro T
    have h1 : T.sum (fun F => if F = newFace Delta.toCombMap faces region then m else 0) ≤ m := by
      rw [Finset.sum_ite_eq']
      split_ifs <;> omega
    have h2 : T.sum (fun F => if F ∈ S then 1 else 0) ≤ S.card := by
      rw [Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one]
      exact Finset.card_le_card fun F hF => (Finset.mem_inter.mp hF).2
    rw [hbf, Finset.sum_add_distrib]
    exact Nat.add_le_add h1 h2
  have hScard : S.card ≤ (Delta.relatorCells.filter (fun C => C.face ∉ faces)).length := by
    rw [hS]
    exact (List.toFinset_card_le _).trans (by simp)
  -- The planar van Kampen lemma on the collapse, with every inner face as a cell.
  obtain ⟨cells, hnd, -, hword, hprod⟩ :=
    exists_relatorCells_of_planar (W := (Set.univ : Set (List (RelLetter G Lambda))))
      (replaceGRegion Delta.toCombMap faces region)
      (replaceGRegion_planar Delta.toCombMap faces region Delta.planar)
      (fun d => Delta.label d.1) (fun d => Delta.label_alpha d.1)
      (keptFace Delta.toCombMap faces region Delta.outerFace hout)
      (replaceGRegionFaceBoundary Delta.toCombMap faces region Delta.faceBoundary)
      (Finset.univ.erase (keptFace Delta.toCombMap faces region Delta.outerFace hout))
      (Finset.notMem_erase _ _) (fun _ _ => Set.mem_univ _)
      (fun f hf hnot => absurd (Finset.mem_erase.mpr ⟨hf, Finset.mem_univ f⟩) hnot)
  have hcell : ∀ C ∈ cells, RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W)
      ((bf ∘ RelatorCell.face) C) C.value := by
    intro C hC
    apply RelatorCell.isRelatorProduct_value
    rw [hword C hC]
    exact hface C.face C.face_ne_outer
  have hprodR : RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W)
      (cells.map (bf ∘ RelatorCell.face)).sum (cells.map RelatorCell.value).prod :=
    RelatorDefectBudget.isRelatorProduct_prod_map_sum _ _ cells hcell
  rw [hprod, replaceGRegionFaceBoundary_keptFace_word Delta faces region Delta.outerFace hout]
    at hprodR
  refine ⟨_, ?_, hprodR⟩
  have hsum : (cells.map (bf ∘ RelatorCell.face)).sum =
      (cells.map RelatorCell.face).toFinset.sum bf := by
    rw [List.sum_toFinset bf hnd, List.map_map]
  have hT := hbound (cells.map RelatorCell.face).toFinset
  omega

open scoped Classical in
/-- **Relator cells inside a disc region of a least-area diagram.**  In a least-area diagram,
a filling of the boundary word of a disc region away from the exterior needs at least as many
relators as the region has relator cells. -/
theorem DiscDiagram.LeastArea.length_filter_mem_le {W : Set (List (RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} (hlea : Delta.LeastArea)
    (faces : Finset Delta.toCombMap.Face) (region : IsDiscRegion Delta.toCombMap faces)
    (hout : Delta.outerFace ∉ faces) {m : ℕ}
    (hm : RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) m
      (RelLetter.listVal (Embedded.dartWord Delta region.toBoundaryCycle.cycle))) :
    (Delta.relatorCells.filter (fun C => C.face ∈ faces)).length ≤ m := by
  obtain ⟨n, hn, hprod⟩ := Delta.exists_isRelatorProduct_of_discRegion faces region hout hm
  have hle : Delta.relatorCells.length ≤ n := hlea hprod
  have hsplit : Delta.relatorCells.length =
      (Delta.relatorCells.filter (fun C => C.face ∈ faces)).length +
        (Delta.relatorCells.filter (fun C => C.face ∉ faces)).length := by
    rw [List.length_eq_length_filter_add (l := Delta.relatorCells)
      (fun C => decide (C.face ∈ faces))]
    simp only [decide_not]
  omega

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.RelatorDefectBudget.isRelatorProduct_prod_map_sum
#audit_axioms GroupApproximation.GGT.VanKampen.RelatorCell.isRelatorProduct_value
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.replaceGRegionFaceBoundary_keptFace_word
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.replaceGRegionFaceBoundary_newFace_word
#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.exists_isRelatorProduct_of_discRegion
#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.LeastArea.length_filter_mem_le
