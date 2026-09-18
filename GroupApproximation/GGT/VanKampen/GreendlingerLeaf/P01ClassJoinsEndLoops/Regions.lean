import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.Separation
import GroupApproximation.Meta.AxiomGuard

/-!
# End loops of the class producer: the dart after a pocket on a region

Cases 2 and 3 (region part) of the route in `FaceOrbit.lean`.  If `p = f^J x` lies on an arc
of a region at the cell, then either `d = f^s x` (`s < J`) lies on the same arc, or the reverse
of `d` is among the reverses of the `L` face predecessors of the first dart of the arc.  If the
face of `α p` is a face of a region, then `α p` is a boundary dart of the region: either `p` lies
on an arc of the region at the cell, or `α p` lies on a side of the region.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

section Regions

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {i : Fin X.rCellCount}

/-- The dart after a pocket on an arc of the cell. -/
theorem case_arc {x d : X.toCombMap.Dart} {J s L : ℕ} (hs : s < J)
    (hd : (X.toCombMap.facePerm ^ s) x = d) (hJL : J ≤ L)
    {cycle : List X.toCombMap.Dart} (hcyc : cycle = cellDarts X i) (A : CyclicArc cycle)
    (hp : (X.toCombMap.facePerm ^ J) x ∈ A.darts) :
    d ∈ A.darts ∨ ∃ st ∈ A.darts.head?, X.toCombMap.alpha d ∈ back X.toCombMap st L := by
  obtain ⟨y, _, hA⟩ := arc_seg hcyc A
  rw [hA] at hp ⊢
  obtain ⟨r, hr, hpr⟩ := mem_seg_iff.mp hp
  by_cases hrs : J - s ≤ r
  · left
    refine mem_seg_iff.mpr ⟨r - (J - s), by omega, ?_⟩
    rw [← hd]
    apply pow_shift (t := J - s)
    rw [Nat.sub_add_cancel hrs, hpr, show s + (J - s) = J by omega]
  · right
    have h0 : (X.toCombMap.facePerm ^ (0 + r)) y =
        (X.toCombMap.facePerm ^ ((J - s - r - 1 + 1) + r)) d := by
      rw [Nat.zero_add, hpr, ← hd, ← pow_apply_add,
        show J - s - r - 1 + 1 + r + s = J by omega]
    have hst := pow_shift h0
    rw [pow_zero, Equiv.Perm.one_apply] at hst
    exact ⟨y, Option.mem_def.mpr (head?_seg _ (by omega)), mem_back hst.symm (by omega)⟩

/-- The reverse of `d` among the reverses of the face predecessors of `α (α p)`. -/
theorem alpha_mem_back_p {x d : X.toCombMap.Dart} {J s L : ℕ} (hs : s < J)
    (hd : (X.toCombMap.facePerm ^ s) x = d) (hJL : J ≤ L) :
    X.toCombMap.alpha d ∈ back X.toCombMap
      (X.toCombMap.alpha (X.toCombMap.alpha ((X.toCombMap.facePerm ^ J) x))) L := by
  rw [X.toCombMap.alpha_involutive ((X.toCombMap.facePerm ^ J) x)]
  refine mem_back (t := J - s - 1) ?_ (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ J - s), ← hd, ← pow_apply_add, Nat.sub_add_cancel hs.le]

/-- The two ways a dart lies on the actual darts of a region at a cell. -/
theorem mem_cellArcDarts_cases {D : RelGenSet G Lambda} {eps : ℕ} (a : RegionCandidate D eps X)
    {p : X.toCombMap.Dart} (hp : p ∈ a.cellArcDarts i) :
    (a.2.source = i ∧ p ∈ a.2.sourceArc.darts) ∨
      (a.2.target = some i ∧ p ∈ a.2.targetArc.darts) := by
  rcases Finset.mem_union.mp hp with hs | ht
  · split at hs
    next heq => exact Or.inl ⟨heq, List.mem_toFinset.mp hs⟩
    next => simp at hs
  · split at ht
    next heq => exact Or.inr ⟨heq, List.mem_toFinset.mp ht⟩
    next => simp at ht

/-- When no relator word has value one, no region contains a relator cell. -/
theorem cell_face_not_mem {D : RelGenSet G Lambda} {eps : ℕ}
    (hvalue : ∀ C ∈ X.relatorCells, RelLetter.listVal C.word ≠ 1)
    (a : RegionCandidate D eps X) : (cell X i).face ∉ a.1 := by
  intro hmem
  have hone := (a.2.boundary.all_gCells _ hmem).2
  apply hvalue (cell X i) (cell_mem X i)
  rw [X.relatorCell_word (cell X i) (cell_mem X i)]
  exact hone

/-- The dart after a pocket, with its reverse on a face of a region. -/
theorem case_region {D : RelGenSet G Lambda} {eps : ℕ}
    (hvalue : ∀ C ∈ X.relatorCells, RelLetter.listVal C.word ≠ 1)
    (a : RegionCandidate D eps X) {p : X.toCombMap.Dart} (hp : p ∈ cellDarts X i)
    (ha : X.toCombMap.faceOf (X.toCombMap.alpha p) ∈ a.1) :
    p ∈ a.cellArcDarts i ∨ X.toCombMap.alpha p ∈ a.2.rightSide ++ a.2.leftSide := by
  have hnot : (cell X i).face ∉ a.1 := cell_face_not_mem hvalue a
  have hbd : X.toCombMap.alpha p ∈ a.2.boundary.cycle := by
    refine (a.2.boundary.cycle_mem_iff _).mpr (And.intro ha ?_)
    rw [X.toCombMap.alpha_involutive p, faceOf_of_mem_cellDarts hp]
    exact hnot
  rw [a.2.boundary_decomposition] at hbd
  rcases List.mem_append.mp hbd with h1 | h4
  · rcases List.mem_append.mp h1 with h2 | h3
    · rcases List.mem_append.mp h2 with hsrc | hright
      · left
        have hpa := mem_of_alpha_mem_reverseDarts a.2.sourceArc hsrc
        have hsi : a.2.source = i := cell_face_injective X
          ((faceOf_of_mem_cellDarts (a.2.sourceArc.mem_cycle_of_mem_darts hpa)).symm.trans
            (faceOf_of_mem_cellDarts hp))
        refine Finset.mem_union.mpr (Or.inl ?_)
        split
        next => exact List.mem_toFinset.mpr hpa
        next hne => exact (hne hsi).elim
      · right
        exact List.mem_append.mpr (Or.inl hright)
    · rcases alpha_mem_targetBoundaryDarts a.2.target a.2.targetArc p h3 with
        hout | ⟨j, hj, hpj, hface⟩
      · exact ((cell X i).face_ne_outer ((faceOf_of_mem_cellDarts hp).symm.trans hout)).elim
      · left
        have hji : j = i := cell_face_injective X (hface.symm.trans (faceOf_of_mem_cellDarts hp))
        rw [hji] at hj
        refine Finset.mem_union.mpr (Or.inr ?_)
        split
        next => exact List.mem_toFinset.mpr hpj
        next hne => exact (hne hj).elim
  · right
    exact List.mem_append.mpr (Or.inr h4)

end Regions

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.case_arc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.alpha_mem_back_p
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.mem_cellArcDarts_cases
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.cell_face_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.case_region
