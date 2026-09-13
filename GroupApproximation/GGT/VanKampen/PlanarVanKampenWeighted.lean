import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPart
import GroupApproximation.GGT.HullSCSmallCancellation
import GroupApproximation.Meta.AxiomGuard

/-!
# The weighted planar van Kampen lemma

The planar van Kampen lemma (`isRelatorProduct_of_planar`) counts one relator for each relator
face.  Here each relator face `f` carries a weight `wt f`: if the word of `f` is a product of
`wt f` signed conjugates of relators, the outer word is a product of `∑ f, wt f` of them.
The proof reads the cellular form (`exists_cellFactors_of_planar`), in which the outer word is
a product of conjugates of face words, one for each relator face, and adds the budgets.

The exact index matters: `IsRelatorProduct` is not monotone in its index, so a product with
exactly `n` factors is more than one with at most `n`.

* `isRelatorProduct_of_planar_weighted`: the weighted lemma, for face cycles.
* `isRelatorProduct_of_planar_unweighted`: the case `wt ≡ 1`.
* `planarVanKampenWeighted`: the weighted lemma, for a choice of face boundaries.
* `DiscDiagram.isRelatorProduct_filter_add_of_discRegion`: collapse a disc region of `Δ` away
  from the exterior into one face of weight `m`.  If the boundary word of the region is a
  product of `m` relators, the boundary of `Δ` is a product of exactly `m` plus the number of
  relator cells outside the region.
* `DiscDiagram.isRelatorProduct_rCellCount_sub_add_of_discRegion`: the same index written as
  `rCellCount - #inside + m`.
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC Surgery.MapCollapse

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}

/-- Rotating a word keeps its relator budget. -/
theorem isRelatorProduct_rotate {R : Set G} {m : ℕ} (l : List (RelLetter G Lambda)) {k : ℕ}
    (hk : k ≤ l.length) (h : RelatorDefectBudget.IsRelatorProduct R m (RelLetter.listVal l)) :
    RelatorDefectBudget.IsRelatorProduct R m (RelLetter.listVal (l.rotate k)) := by
  rw [RelWord.listVal_rotate l hk]
  simpa using h.conj (RelLetter.listVal (l.take k))⁻¹

/-- **The weighted planar van Kampen lemma.**  In a planar map, let each relator face `f` read
a product of `wt f` signed conjugates of relators, and let every other face except the outer
one read `1`.  Then the outer face reads a product of `∑ f ∈ relFaces, wt f` of them. -/
theorem isRelatorProduct_of_planar_weighted {R : Set G} (M : CombMap.{v}) (hplanar : M.IsPlanar)
    (label : M.Dart → RelLetter G Lambda)
    (label_alpha : ∀ d, label (M.alpha d) = RelWord.inv (label d))
    (relFaces : Finset M.Face) (wt : M.Face → ℕ) (lO : List M.Dart) (hO : M.IsFaceCycle lO)
    (hOrel : M.faceOf (lO.head hO.ne_nil) ∉ relFaces)
    (hrel : ∀ (l : List M.Dart) (hl : M.IsFaceCycle l), M.faceOf (l.head hl.ne_nil) ∈ relFaces →
      RelatorDefectBudget.IsRelatorProduct R (wt (M.faceOf (l.head hl.ne_nil)))
        (RelLetter.listVal (l.map label)))
    (htriv : ∀ (l : List M.Dart) (hl : M.IsFaceCycle l),
      M.faceOf (l.head hl.ne_nil) ≠ M.faceOf (lO.head hO.ne_nil) →
      M.faceOf (l.head hl.ne_nil) ∉ relFaces → RelLetter.listVal (l.map label) = 1) :
    RelatorDefectBudget.IsRelatorProduct R (∑ f ∈ relFaces, wt f)
      (RelLetter.listVal (lO.map label)) := by
  classical
  obtain ⟨factors, hnd, hiff, hfac, hprod⟩ :=
    exists_cellFactors_of_planar M.dartCount M rfl hplanar label label_alpha relFaces lO hO hOrel
      htriv
  have hfac' : ∀ y ∈ factors, RelatorDefectBudget.IsRelatorProduct R (wt y.1) y.2 := by
    intro y hy
    obtain ⟨l, hl, c, hf, hx | hx⟩ := hfac y hy
    · have hrl := hrel l hl (by rw [hf]; exact (hiff y.1).mp (List.mem_map.mpr ⟨y, hy, rfl⟩))
      rw [hf] at hrl
      rw [hx]
      exact hrl.conj c
    · have hrl := hrel l hl (by rw [hf]; exact (hiff y.1).mp (List.mem_map.mpr ⟨y, hy, rfl⟩))
      rw [hf] at hrl
      rw [hx]
      exact hrl.inv.conj c
  have hsum := RelatorDefectBudget.isRelatorProduct_prod_map_sum (wt ∘ Prod.fst) Prod.snd
    factors hfac'
  have hfin : (factors.map Prod.fst).toFinset = relFaces := by
    ext f
    rw [List.mem_toFinset]
    exact hiff f
  rw [← hfin, List.sum_toFinset wt hnd, List.map_map, ← hprod]
  exact hsum

/-- The case `wt ≡ 1` of `isRelatorProduct_of_planar_weighted`. -/
theorem isRelatorProduct_of_planar_unweighted {R : Set G} (M : CombMap.{v})
    (hplanar : M.IsPlanar) (label : M.Dart → RelLetter G Lambda)
    (label_alpha : ∀ d, label (M.alpha d) = RelWord.inv (label d))
    (relFaces : Finset M.Face) (lO : List M.Dart) (hO : M.IsFaceCycle lO)
    (hOrel : M.faceOf (lO.head hO.ne_nil) ∉ relFaces)
    (hrel : ∀ (l : List M.Dart) (hl : M.IsFaceCycle l), M.faceOf (l.head hl.ne_nil) ∈ relFaces →
      RelatorDefectBudget.IsRelatorProduct R 1 (RelLetter.listVal (l.map label)))
    (htriv : ∀ (l : List M.Dart) (hl : M.IsFaceCycle l),
      M.faceOf (l.head hl.ne_nil) ≠ M.faceOf (lO.head hO.ne_nil) →
      M.faceOf (l.head hl.ne_nil) ∉ relFaces → RelLetter.listVal (l.map label) = 1) :
    RelatorDefectBudget.IsRelatorProduct R relFaces.card (RelLetter.listVal (lO.map label)) := by
  have h := isRelatorProduct_of_planar_weighted M hplanar label label_alpha relFaces (fun _ => 1)
    lO hO hOrel hrel htriv
  simpa using h

/-- **The weighted planar van Kampen lemma, for face boundaries.** -/
theorem planarVanKampenWeighted {R : Set G} (M : CombMap.{v}) (hplanar : M.IsPlanar)
    (label : M.Dart → RelLetter G Lambda)
    (label_alpha : ∀ d, label (M.alpha d) = RelWord.inv (label d))
    (O : M.Face) (FB : ∀ f, FaceBoundary M f) (relFaces : Finset M.Face) (wt : M.Face → ℕ)
    (hOrel : O ∉ relFaces)
    (hrel : ∀ f ∈ relFaces, RelatorDefectBudget.IsRelatorProduct R (wt f)
      (RelLetter.listVal ((FB f).darts.map label)))
    (htriv : ∀ f, f ≠ O → f ∉ relFaces → RelLetter.listVal ((FB f).darts.map label) = 1) :
    RelatorDefectBudget.IsRelatorProduct R (∑ f ∈ relFaces, wt f)
      (RelLetter.listVal ((FB O).darts.map label)) := by
  refine isRelatorProduct_of_planar_weighted M hplanar label label_alpha relFaces wt (FB O).darts
    (FB O).isFaceCycle (by rw [FaceBoundary.faceOf_head]; exact hOrel) ?_ ?_
  · intro l hl hf
    obtain ⟨F, hFl⟩ : ∃ F, M.faceOf (l.head hl.ne_nil) = F := ⟨_, rfl⟩
    rw [hFl] at hf ⊢
    obtain ⟨k, hk, hrot⟩ := (FB F).isFaceCycle.exists_rotate_eq hl
      ((FaceBoundary.faceOf_head (FB F)).trans hFl.symm)
    have hk' : k ≤ ((FB F).darts.map label).length := by rw [List.length_map]; exact hk
    rw [← hrot, List.map_rotate]
    exact isRelatorProduct_rotate _ hk' (hrel F hf)
  · intro l hl hne hf
    obtain ⟨F, hFl⟩ : ∃ F, M.faceOf (l.head hl.ne_nil) = F := ⟨_, rfl⟩
    rw [hFl, FaceBoundary.faceOf_head] at hne
    rw [hFl] at hf
    obtain ⟨k, hk, hrot⟩ := (FB F).isFaceCycle.exists_rotate_eq hl
      ((FaceBoundary.faceOf_head (FB F)).trans hFl.symm)
    have hk' : k ≤ ((FB F).darts.map label).length := by rw [List.length_map]; exact hk
    rw [← hrot, List.map_rotate, RelWord.listVal_rotate _ hk', htriv F hne hf]
    simp

open scoped Classical in
/-- **The outer part of a disc region, exact index.**  Let `faces` be a disc region of `Δ` away
from the exterior face.  If the boundary word of the region is a product of `m` signed
conjugates of relators, the boundary of `Δ` is a product of exactly `m` plus the number of
relator cells outside the region.  Collapse the region into one face and apply the weighted
planar van Kampen lemma, with weight `m` on the new face and `1` on each kept relator face. -/
theorem DiscDiagram.isRelatorProduct_filter_add_of_discRegion
    {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
    (region : IsDiscRegion Delta.toCombMap faces) (hout : Delta.outerFace ∉ faces) {m : ℕ}
    (hm : RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) m
      (RelLetter.listVal (Embedded.dartWord Delta region.toBoundaryCycle.cycle))) :
    RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W)
      ((Delta.relatorCells.filter (fun C => C.face ∉ faces)).length + m) Delta.boundaryValue := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (replaceGRegion Delta.toCombMap faces region).Face,
      S = ((Delta.relatorCells.filter (fun C => C.face ∉ faces)).map
        (fun C => if hC : C.face ∈ faces then newFace Delta.toCombMap faces region
          else keptFace Delta.toCombMap faces region C.face hC)).toFinset := ⟨_, rfl⟩
  obtain ⟨wt, hwt⟩ : ∃ wt : (replaceGRegion Delta.toCombMap faces region).Face → ℕ,
      wt = fun F => if F = newFace Delta.toCombMap faces region then m else 1 := ⟨_, rfl⟩
  -- The faces of `S` are the kept relator faces.
  have hSmem : ∀ F ∈ S, ∃ C ∈ Delta.relatorCells, ∃ hC : C.face ∉ faces,
      keptFace Delta.toCombMap faces region C.face hC = F := by
    intro F hF
    rw [hS, List.mem_toFinset] at hF
    obtain ⟨C, hC, hCF⟩ := List.mem_map.mp hF
    have hC' := List.mem_filter.mp hC
    have hCout : C.face ∉ faces := by simpa using hC'.2
    simp only [dif_neg hCout] at hCF
    exact ⟨C, hC'.1, hCout, hCF⟩
  have hnS : newFace Delta.toCombMap faces region ∉ S := fun hF => by
    obtain ⟨C, -, hCout, hCF⟩ := hSmem _ hF
    exact keptFace_ne_newFace Delta.toCombMap faces region C.face hCout hCF
  have houter : keptFace Delta.toCombMap faces region Delta.outerFace hout ∉
      insert (newFace Delta.toCombMap faces region) S := by
    rw [Finset.mem_insert, not_or]
    refine ⟨keptFace_ne_newFace Delta.toCombMap faces region _ hout, fun hF => ?_⟩
    obtain ⟨C, -, hCout, hCF⟩ := hSmem _ hF
    exact C.face_ne_outer (keptFace_inj Delta.toCombMap faces region _ _ hCout hout hCF)
  -- The budget of each relator face of the collapse.
  have hrel : ∀ F ∈ insert (newFace Delta.toCombMap faces region) S,
      RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) (wt F)
        (RelLetter.listVal ((replaceGRegionFaceBoundary Delta.toCombMap faces region
          Delta.faceBoundary F).darts.map (fun d => Delta.label d.1))) := by
    intro F hF
    rcases Finset.mem_insert.mp hF with rfl | hFS
    · have hw : wt (newFace Delta.toCombMap faces region) = m := by simp [hwt]
      rw [hw, replaceGRegionFaceBoundary_newFace_word Delta faces region]
      exact hm
    · obtain ⟨C, hC, hCout, rfl⟩ := hSmem F hFS
      have hw : wt (keptFace Delta.toCombMap faces region C.face hCout) = 1 := by
        simp [hwt, keptFace_ne_newFace Delta.toCombMap faces region _ hCout]
      rw [hw, replaceGRegionFaceBoundary_keptFace_word Delta faces region C.face hCout,
        DiscDiagram.faceWord, ← Delta.relatorCell_word C hC]
      exact RelatorDefectBudget.IsRelatorProduct.base ⟨C.word, C.word_mem, rfl⟩
  -- Every other inner face of the collapse is a kept `G`-face.
  have htriv : ∀ F, F ≠ keptFace Delta.toCombMap faces region Delta.outerFace hout →
      F ∉ insert (newFace Delta.toCombMap faces region) S →
      RelLetter.listVal ((replaceGRegionFaceBoundary Delta.toCombMap faces region
        Delta.faceBoundary F).darts.map (fun d => Delta.label d.1)) = 1 := by
    intro F hF hnot
    have hnew : F ≠ newFace Delta.toCombMap faces region :=
      fun h => hnot (Finset.mem_insert.mpr (Or.inl h))
    have hFS : F ∉ S := fun h => hnot (Finset.mem_insert.mpr (Or.inr h))
    obtain ⟨g, hg, rfl⟩ := exists_keptFace_of_ne_newFace Delta.toCombMap faces region F hnew
    have hgo : g ≠ Delta.outerFace := fun h =>
      hF (keptFace_congr Delta.toCombMap faces region _ _ hg hout h)
    rw [replaceGRegionFaceBoundary_keptFace_word Delta faces region g hg]
    rcases Delta.inner_face g hgo with ⟨C, hC, rfl⟩ | hone
    · exfalso
      apply hFS
      rw [hS, List.mem_toFinset]
      exact List.mem_map.mpr ⟨C, List.mem_filter.mpr ⟨hC, by simpa using hg⟩, dif_neg hg⟩
    · exact hone
  have hmain := planarVanKampenWeighted (replaceGRegion Delta.toCombMap faces region)
    (replaceGRegion_planar Delta.toCombMap faces region Delta.planar)
    (fun d => Delta.label d.1) (fun d => Delta.label_alpha d.1)
    (keptFace Delta.toCombMap faces region Delta.outerFace hout)
    (replaceGRegionFaceBoundary Delta.toCombMap faces region Delta.faceBoundary)
    (insert (newFace Delta.toCombMap faces region) S) wt houter hrel htriv
  -- The total weight.
  have hnodup : ((Delta.relatorCells.filter (fun C => C.face ∉ faces)).map
      (fun C => if hC : C.face ∈ faces then newFace Delta.toCombMap faces region
        else keptFace Delta.toCombMap faces region C.face hC)).Nodup := by
    refine List.Nodup.map_on ?_ ((List.Nodup.of_map _ Delta.relatorCell_faces_nodup).filter _)
    intro C hC C' hC' hCC'
    have hC1 := List.mem_filter.mp hC
    have hC1' := List.mem_filter.mp hC'
    have hCout : C.face ∉ faces := by simpa using hC1.2
    have hC'out : C'.face ∉ faces := by simpa using hC1'.2
    simp only [dif_neg hCout, dif_neg hC'out] at hCC'
    exact List.inj_on_of_nodup_map Delta.relatorCell_faces_nodup hC1.1 hC1'.1
      (keptFace_inj Delta.toCombMap faces region _ _ hCout hC'out hCC')
  have hScard : S.card = (Delta.relatorCells.filter (fun C => C.face ∉ faces)).length := by
    rw [hS, List.toFinset_card_of_nodup hnodup, List.length_map]
  have hSsum : ∑ F ∈ S, wt F = S.card := by
    calc ∑ F ∈ S, wt F = ∑ _F ∈ S, (1 : ℕ) :=
          Finset.sum_congr rfl fun F hF => by
            have hFn : F ≠ newFace Delta.toCombMap faces region := fun h => hnS (h ▸ hF)
            simp [hwt, hFn]
      _ = S.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  have hwn : wt (newFace Delta.toCombMap faces region) = m := by simp [hwt]
  have hsum : ∑ F ∈ insert (newFace Delta.toCombMap faces region) S, wt F =
      (Delta.relatorCells.filter (fun C => C.face ∉ faces)).length + m := by
    rw [Finset.sum_insert hnS, hSsum, hScard, hwn]
    omega
  rw [hsum, replaceGRegionFaceBoundary_keptFace_word Delta faces region Delta.outerFace hout]
    at hmain
  rw [DiscDiagram.boundaryValue, DiscDiagram.boundaryWord, RelWord.listVal_revInv]
  exact hmain.inv

open scoped Classical in
/-- `DiscDiagram.isRelatorProduct_filter_add_of_discRegion`, with the index written as the
number of relator cells, minus those inside the region, plus `m`. -/
theorem DiscDiagram.isRelatorProduct_rCellCount_sub_add_of_discRegion
    {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
    (region : IsDiscRegion Delta.toCombMap faces) (hout : Delta.outerFace ∉ faces) {m : ℕ}
    (hm : RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) m
      (RelLetter.listVal (Embedded.dartWord Delta region.toBoundaryCycle.cycle))) :
    RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W)
      (Delta.rCellCount - (Delta.relatorCells.filter (fun C => C.face ∈ faces)).length + m)
      Delta.boundaryValue := by
  have hsplit : Delta.relatorCells.length =
      (Delta.relatorCells.filter (fun C => C.face ∈ faces)).length +
        (Delta.relatorCells.filter (fun C => C.face ∉ faces)).length := by
    rw [List.length_eq_length_filter_add (l := Delta.relatorCells)
      (fun C => decide (C.face ∈ faces))]
    simp only [decide_not]
  have hidx : Delta.rCellCount - (Delta.relatorCells.filter (fun C => C.face ∈ faces)).length +
      m = (Delta.relatorCells.filter (fun C => C.face ∉ faces)).length + m := by
    rw [DiscDiagram.rCellCount]
    omega
  rw [hidx]
  exact Delta.isRelatorProduct_filter_add_of_discRegion faces region hout hm

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.isRelatorProduct_rotate
#audit_axioms GroupApproximation.GGT.VanKampen.isRelatorProduct_of_planar_weighted
#audit_axioms GroupApproximation.GGT.VanKampen.isRelatorProduct_of_planar_unweighted
#audit_axioms GroupApproximation.GGT.VanKampen.planarVanKampenWeighted
#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.isRelatorProduct_filter_add_of_discRegion
#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.isRelatorProduct_rCellCount_sub_add_of_discRegion
