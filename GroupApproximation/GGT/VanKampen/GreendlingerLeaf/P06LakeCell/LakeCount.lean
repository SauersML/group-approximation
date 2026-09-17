import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.LakeDef
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, case (d): a lake holds fewer relator cells than the diagram

Lane `gl-p06-10` of `lanes/carto-gl-p06.md`.  Certifies no printed sentence on its own.

Let `K : CellPocketFaceSet D eps X i j` and let `Π_k` be a cell off `K.faces`.

* `lake_rCellCount_lt`: the indices `m` with `Π_m ∈ lakeOf K k` number fewer than
  `X.rCellCount`.  Proof: they form a subset of `Finset.univ` missing `K.kept`
  (`kept_not_mem_lake`), so `Finset.card_lt_card` applies.
* `lake_erase_rCellCount_add_two_le`: the indices `m ≠ k` with `Π_m ∈ lakeOf K k` number at most
  `X.rCellCount - 2`.  Proof: they lie in `(univ.erase k).erase K.kept`, and `K.kept ≠ k`
  (`kept_ne_of_not_mem`), so that set has `X.rCellCount - 2` elements and `X.rCellCount ≥ 2`.
  Removing `Π_k` from its lake therefore leaves strictly fewer than `X.rCellCount - 1` relator
  cells, as lane 11 needs for `OsinLemma97Below`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

universe u w v

open Embedded HullSC WordMetric Surgery.MapCollapse
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A lake holds fewer relator cells than the diagram** (`lake_rCellCount_lt`): the kept cell
is off the lake. -/
theorem lake_rCellCount_lt (K : CellPocketFaceSet D eps X i j) {k : Fin X.rCellCount}
    (hk : (cell X k).face ∉ K.faces) :
    (Finset.univ.filter fun m : Fin X.rCellCount => (cell X m).face ∈ lakeOf K k).card <
      X.rCellCount := by
  have hsub : (Finset.univ.filter fun m : Fin X.rCellCount => (cell X m).face ∈ lakeOf K k) ⊆
      Finset.univ :=
    Finset.filter_subset _ _
  have hss : (Finset.univ.filter fun m : Fin X.rCellCount => (cell X m).face ∈ lakeOf K k) ⊂
      Finset.univ := by
    refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨K.kept, Finset.mem_univ _, ?_⟩
    intro hmem
    exact kept_not_mem_lake K hk (Finset.mem_filter.mp hmem).2
  calc (Finset.univ.filter fun m : Fin X.rCellCount => (cell X m).face ∈ lakeOf K k).card
      < (Finset.univ : Finset (Fin X.rCellCount)).card := Finset.card_lt_card hss
    _ = X.rCellCount := Finset.card_fin X.rCellCount

/-- The lake of `Π_i` holds fewer relator cells than the diagram. -/
theorem firstLake_rCellCount_lt (K : CellPocketFaceSet D eps X i j) :
    (Finset.univ.filter fun m : Fin X.rCellCount => (cell X m).face ∈ lakeOf K i).card <
      X.rCellCount :=
  lake_rCellCount_lt K K.first_not_mem

/-- The lake of `Π_j` holds fewer relator cells than the diagram. -/
theorem secondLake_rCellCount_lt (K : CellPocketFaceSet D eps X i j) :
    (Finset.univ.filter fun m : Fin X.rCellCount => (cell X m).face ∈ lakeOf K j).card <
      X.rCellCount :=
  lake_rCellCount_lt K K.second_not_mem

/-- **The lake minus its own cell holds at most `X.rCellCount - 2` relator cells.**  Both the
cell `k` and the kept cell are missing. -/
theorem lake_erase_rCellCount_add_two_le (K : CellPocketFaceSet D eps X i j)
    {k : Fin X.rCellCount} (hk : (cell X k).face ∉ K.faces) :
    (Finset.univ.filter fun m : Fin X.rCellCount =>
        (cell X m).face ∈ lakeOf K k ∧ m ≠ k).card + 2 ≤ X.rCellCount := by
  have hkept : K.kept ∈ (Finset.univ : Finset (Fin X.rCellCount)).erase k :=
    Finset.mem_erase.mpr ⟨kept_ne_of_not_mem K hk, Finset.mem_univ _⟩
  have hsub : (Finset.univ.filter fun m : Fin X.rCellCount =>
        (cell X m).face ∈ lakeOf K k ∧ m ≠ k) ⊆
      ((Finset.univ : Finset (Fin X.rCellCount)).erase k).erase K.kept := by
    intro m hm
    have hm' := (Finset.mem_filter.mp hm).2
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨hm'.2, Finset.mem_univ _⟩⟩
    intro hmk
    apply kept_not_mem_lake K hk
    rw [← hmk]
    exact hm'.1
  have hle := Finset.card_le_card hsub
  have hcard₂ : (((Finset.univ : Finset (Fin X.rCellCount)).erase k).erase K.kept).card =
      ((Finset.univ : Finset (Fin X.rCellCount)).erase k).card - 1 :=
    Finset.card_erase_of_mem hkept
  have hcard₁ : ((Finset.univ : Finset (Fin X.rCellCount)).erase k).card = X.rCellCount - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_fin]
  have hpos : 0 < ((Finset.univ : Finset (Fin X.rCellCount)).erase k).card :=
    Finset.card_pos.mpr ⟨K.kept, hkept⟩
  omega

/-- The lake of `Π_i` minus `Π_i` holds at most `X.rCellCount - 2` relator cells. -/
theorem firstLake_erase_rCellCount_add_two_le (K : CellPocketFaceSet D eps X i j) :
    (Finset.univ.filter fun m : Fin X.rCellCount =>
        (cell X m).face ∈ lakeOf K i ∧ m ≠ i).card + 2 ≤ X.rCellCount :=
  lake_erase_rCellCount_add_two_le K K.first_not_mem

/-- The lake of `Π_j` minus `Π_j` holds at most `X.rCellCount - 2` relator cells. -/
theorem secondLake_erase_rCellCount_add_two_le (K : CellPocketFaceSet D eps X i j) :
    (Finset.univ.filter fun m : Fin X.rCellCount =>
        (cell X m).face ∈ lakeOf K j ∧ m ≠ j).card + 2 ≤ X.rCellCount :=
  lake_erase_rCellCount_add_two_le K K.second_not_mem

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.lake_rCellCount_lt
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.firstLake_rCellCount_lt
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.secondLake_rCellCount_lt
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.lake_erase_rCellCount_add_two_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.firstLake_erase_rCellCount_add_two_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.secondLake_erase_rCellCount_add_two_le
