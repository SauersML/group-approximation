import GroupApproximation.GGT.KazhdanHypSharpExistenceAssembly
import GroupApproximation.GGT.VanKampen.SurgeryFacePartition
import GroupApproximation.Algebra.GroupTorsionFree
import GroupApproximation.Meta.AxiomGuard
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# The cactus base-cell deletion producer is refuted, and circular per table

`KazhdanHypSharpExistenceAssembly.sharpExistence_of_checkedTable` takes four
van Kampen producers.  The first torsion-freeness producer is
`CactusBaseCellDeletionProducer`: for every triangular table, every nontrivial
torsion element and every word representing it, a planar disc diagram `Δ` over
the triangle relator words together with a `VanKampen.CactusBaseCellDeletion Δ`
whose replacement has the literal power boundary.

**That structure is uninhabited whenever the boundary is freely nontrivial.**
A `CactusBaseCellDeletion` replaces a set `faces` of `G`-faces by
`Surgery.MapCollapse.replaceGRegion`, which returns the old faces outside the
region *plus one new face* (`replaceGRegionFaceEquiv`), and it demands that the
replacement is relator-only (`RelatorCellCover`) with the same number of relator
cells (`GRegionReplacement.cells`).  Every relator face lies outside the region
(its word is freely nontrivial) and so does the outer face (the boundary word is
freely nontrivial), so the replacement has at least `k + 1` inner faces for its
`k` relator cells — while relator-only coverage forces exactly `k`.  This is
`CactusBaseCellDeletion.listVal_boundaryWord_eq_one` below.

Consequences, all proved here:

* `isPowerTorsionFree_of_cactusBaseCellDeletionForPower`: the producer at one
  table already *implies* torsion-freeness of that table's group (the literal
  boundary `w ^ n` would be freely trivial, so `w` is freely trivial);
* `cactusBaseCellDeletionForPower_iff`: per table the producer is **equivalent**
  to torsion-freeness, so for the checked `W(8)` tables it is exactly the theorem
  the extraction is meant to prove, not an input towards it;
* `not_cactusBaseCellDeletionProducer`: the universal producer is **false**,
  witnessed by the one-generator table `x x x`, whose group `ℤ/3` has torsion.

The replacement input the extraction actually needs is a relator-only literal
filling (van Kampen's lemma for the triangle relators): a disc diagram with
boundary exactly `(List.replicate n (word.map signedFreeRelLetter)).flatten`
and `RelatorOnly T`, which is true for every table, as
`GirthEightPrimitives2.nonempty_powerDiscCandidate_of_literalFilling` already
consumes.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

/-! ## Face count of a replaced region -/

/-- Replacing a disc region by `replaceGRegion` keeps the faces outside the
region and adds exactly one face. -/
theorem Surgery.MapCollapse.faceCount_replaceGRegion (M : CombMap.{v})
    (faces : Finset M.Face) (region : Surgery.MapCollapse.IsDiscRegion M faces) :
    (Surgery.MapCollapse.replaceGRegion M faces region).faceCount =
      Nat.card {f : M.Face // f ∉ faces} + 1 := by
  rw [CombMap.faceCount,
    Nat.card_congr (Surgery.MapCollapse.replaceGRegionFaceEquiv M faces region),
    Nat.card_sum, Nat.card_unique]

section Generic

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- The replacement diagram of a cactus deletion has one inner face for every
old face outside the deleted region. -/
theorem CactusBaseCellDeletion.replacement_innerFaceCount
    (C : CactusBaseCellDeletion Delta) :
    C.replacement.diagram.innerFaceCount =
      Nat.card {f : Delta.toCombMap.Face // f ∉ C.faces} := by
  have h1 := C.replacement.diagram.innerFaceCount_add_one_eq_faceCount
  have h2 : C.replacement.diagram.toCombMap.faceCount =
      Nat.card {f : Delta.toCombMap.Face // f ∉ C.faces} + 1 := by
    rw [C.replacement_map_eq]
    exact Surgery.MapCollapse.faceCount_replaceGRegion _ _ _
  omega

/-- A deleted region consists of faces with freely trivial words, so it cannot
contain the outer face of a freely nontrivial boundary. -/
theorem CactusBaseCellDeletion.outerFace_not_mem
    (C : CactusBaseCellDeletion Delta)
    (hb : GGT.RelLetter.listVal Delta.boundaryWord ≠ 1) :
    Delta.outerFace ∉ C.faces := by
  intro hmem
  apply hb
  have h := C.baseWord_one _ hmem
  show GGT.RelLetter.listVal
    (HullSC.RelWord.revInv (Delta.faceWord Delta.outerFace)) = 1
  rw [HullSC.RelWord.listVal_revInv, h, inv_one]

/-- A deleted region cannot contain a relator face whose relator word is freely
nontrivial. -/
theorem CactusBaseCellDeletion.cellFace_not_mem
    (C : CactusBaseCellDeletion Delta)
    (hW : ∀ v ∈ W, GGT.RelLetter.listVal v ≠ 1)
    {cell : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hcell : cell ∈ Delta.relatorCells) :
    cell.face ∉ C.faces := by
  intro hmem
  apply hW cell.word cell.word_mem
  have h := C.baseWord_one _ hmem
  rw [Delta.relatorCell_word cell hcell]
  exact h

/-- The relator faces and the outer face are `rCellCount + 1` distinct faces
outside the deleted region. -/
theorem CactusBaseCellDeletion.rCellCount_add_one_le
    (C : CactusBaseCellDeletion Delta)
    (hW : ∀ v ∈ W, GGT.RelLetter.listVal v ≠ 1)
    (hb : GGT.RelLetter.listVal Delta.boundaryWord ≠ 1) :
    Delta.rCellCount + 1 ≤ Nat.card {f : Delta.toCombMap.Face // f ∉ C.faces} := by
  classical
  have hnot : Delta.outerFace ∉ (Delta.relatorCells.map RelatorCell.face).toFinset := by
    intro hmem
    obtain ⟨cell, _, hface⟩ := List.mem_map.mp (List.mem_toFinset.mp hmem)
    exact cell.face_ne_outer hface
  have hScard : (insert Delta.outerFace
      (Delta.relatorCells.map RelatorCell.face).toFinset).card = Delta.rCellCount + 1 := by
    rw [Finset.card_insert_of_notMem hnot,
      List.toFinset_card_of_nodup Delta.relatorCell_faces_nodup, List.length_map,
      DiscDiagram.rCellCount]
  have hsub : insert Delta.outerFace (Delta.relatorCells.map RelatorCell.face).toFinset ⊆
      Finset.univ.filter (fun f => f ∉ C.faces) := by
    intro f hf
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ f, ?_⟩
    rcases Finset.mem_insert.mp hf with hfo | hmem
    · rw [hfo]
      exact C.outerFace_not_mem hb
    · obtain ⟨cell, hcell, hface⟩ := List.mem_map.mp (List.mem_toFinset.mp hmem)
      rw [← hface]
      exact C.cellFace_not_mem hW hcell
  have hcard : Nat.card {f : Delta.toCombMap.Face // f ∉ C.faces} =
      (Finset.univ.filter (fun f => f ∉ C.faces)).card :=
    Nat.subtype_card _ (fun f => by simp)
  rw [hcard, ← hScard]
  exact Finset.card_le_card hsub

/-- **A cactus base-cell deletion forces a freely trivial boundary.**  The
replacement is relator-only with the old number `k` of relator cells, so it has
exactly `k` inner faces; but the `k` relator faces and the outer face all survive
the region replacement, which adds one more face, giving at least `k + 1`. -/
theorem CactusBaseCellDeletion.listVal_boundaryWord_eq_one
    (C : CactusBaseCellDeletion Delta)
    (hW : ∀ v ∈ W, GGT.RelLetter.listVal v ≠ 1) :
    GGT.RelLetter.listVal Delta.boundaryWord = 1 := by
  by_contra hb
  have hle := C.rCellCount_add_one_le hW hb
  have hinner := C.replacement_innerFaceCount
  have hcover := C.relatorOnly.rCellCount_eq_innerFaceCount
  have hcount := C.replacement.rCellCount_eq
  omega

/-- The structure is empty over a freely nontrivial boundary. -/
theorem CactusBaseCellDeletion.isEmpty_of_listVal_ne_one
    (hW : ∀ v ∈ W, GGT.RelLetter.listVal v ≠ 1)
    (hb : GGT.RelLetter.listVal Delta.boundaryWord ≠ 1) :
    IsEmpty (CactusBaseCellDeletion Delta) :=
  ⟨fun C => hb (C.listVal_boundaryWord_eq_one hW)⟩

/-- The value of an `n`-fold literal repetition is the `n`-th power. -/
theorem listVal_replicate_flatten (v : List (GGT.RelLetter G Lambda)) :
    ∀ n : ℕ, GGT.RelLetter.listVal (List.replicate n v).flatten =
      (GGT.RelLetter.listVal v) ^ n
  | 0 => by
      simp only [List.replicate_zero, List.flatten_nil, GGT.RelLetter.listVal_nil, pow_zero]
  | n + 1 => by
      rw [List.replicate_succ, List.flatten_cons, HullSC.RelWord.listVal_append,
        listVal_replicate_flatten v n, pow_succ']

end Generic

end VanKampen

namespace KazhdanHypCactusDeletionCounting

open GroupApproximation.KazhdanHyp
open VanKampen

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- The parity character of a free group: every generator goes to `1 ∈ ℤ/2`. -/
def parityCharacter (Generator : Type) : FreeGroup Generator →* Multiplicative (ZMod 2) :=
  FreeGroup.lift fun _ => Multiplicative.ofAdd (1 : ZMod 2)

/-- Every signed letter has odd parity. -/
theorem parityCharacter_letterValue (u : TriangularHodgeLayer.SignedGenerator Generator) :
    parityCharacter Generator (FoxBoundary.letterValue FreeGroup.of u) =
      Multiplicative.ofAdd (1 : ZMod 2) := by
  obtain ⟨x, b⟩ := u
  cases b
  · show parityCharacter Generator (FreeGroup.of x)⁻¹ = Multiplicative.ofAdd (1 : ZMod 2)
    rw [map_inv, parityCharacter, FreeGroup.lift_apply_of]
    decide
  · show parityCharacter Generator (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod 2)
    rw [parityCharacter, FreeGroup.lift_apply_of]

/-- **A literal triangle relator is freely nontrivial**: it has odd length. -/
theorem listVal_triangleRelatorWord_ne_one
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (j : TriangleIndex) :
    GGT.RelLetter.listVal (triangleRelatorWord T j) ≠ 1 := by
  intro h
  have h2 := congrArg (parityCharacter Generator) h
  have hval : GGT.RelLetter.listVal (triangleRelatorWord T j) =
      FoxBoundary.letterValue FreeGroup.of (T j 0) *
        (FoxBoundary.letterValue FreeGroup.of (T j 1) *
          (FoxBoundary.letterValue FreeGroup.of (T j 2) * 1)) := by
    simp only [triangleRelatorWord, TriangularHodgeLayer.letters_eq_three, List.map_cons,
      List.map_nil, GGT.RelLetter.listVal, signedFreeRelLetter, GGT.RelLetter.val,
      List.prod_cons, List.prod_nil]
  rw [hval, map_mul, map_mul, map_mul, map_one, parityCharacter_letterValue,
    parityCharacter_letterValue, parityCharacter_letterValue] at h2
  exact absurd h2 (by decide)

/-- Every word of the triangle relator family is freely nontrivial. -/
theorem triangleRelatorWords_listVal_ne_one
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    ∀ v ∈ triangleRelatorWords T, GGT.RelLetter.listVal v ≠ 1 := by
  rintro v ⟨j, rfl⟩
  exact listVal_triangleRelatorWord_ne_one T j

/-- The literal relative word of a signed word spells its free-group element. -/
theorem listVal_map_signedFreeRelLetter
    (word : List (TriangularHodgeLayer.SignedGenerator Generator)) :
    GGT.RelLetter.listVal (word.map signedFreeRelLetter) =
      PresentedGroupRelatorReplay.word word := by
  have h := FoxBoundary.wordValue_freeGroup_map (MonoidHom.id (FreeGroup Generator)) word
  simp only [MonoidHom.id_apply] at h
  rw [← h, GGT.RelLetter.listVal, FoxBoundary.wordValue, List.map_map]
  congr 1

/-! ## The producer at one table is torsion-freeness of that table -/

/-- **The cactus deletion producer at a table implies torsion-freeness.**  For a
nontrivial torsion element with representative `word`, the deletion's boundary
is the literal power, which `listVal_boundaryWord_eq_one` makes freely trivial;
free groups are torsion-free, so `word` is freely trivial and the element is
`1`. -/
theorem isPowerTorsionFree_of_cactusBaseCellDeletionForPower
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (h : GirthEightTorsionExtraction.CactusBaseCellDeletionForPower T) :
    IsPowerTorsionFree (TriangularHodgeLayer.Presented T) := by
  intro g n hn hpow
  by_contra hne
  obtain ⟨word, hword⟩ := GirthEightPrimitives2.exists_signedWord_represents (T := T) g
  obtain ⟨Delta, _hplanar, C, hboundary⟩ := h g n hn hpow hne word hword
  have hDelta : Delta.boundaryWord =
      (List.replicate n (word.map signedFreeRelLetter)).flatten :=
    C.replacement.outerWord_eq.symm.trans hboundary
  have hone := C.listVal_boundaryWord_eq_one (triangleRelatorWords_listVal_ne_one T)
  rw [hDelta, listVal_replicate_flatten, listVal_map_signedFreeRelLetter] at hone
  have hfree : PresentedGroupRelatorReplay.word word = 1 :=
    IsPowerTorsionFree.of_isMulTorsionFree (G := FreeGroup Generator) _ n hn hone
  apply hne
  rw [← hword, hfree, map_one]

/-- **Per table, the cactus deletion producer is equivalent to torsion-freeness.**
The reverse implication is vacuous: in a torsion-free group the producer's
hypotheses are contradictory.  So at a checked table this producer is the
theorem the extraction is meant to prove. -/
theorem cactusBaseCellDeletionForPower_iff
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    GirthEightTorsionExtraction.CactusBaseCellDeletionForPower T ↔
      IsPowerTorsionFree (TriangularHodgeLayer.Presented T) := by
  constructor
  · exact isPowerTorsionFree_of_cactusBaseCellDeletionForPower T
  · intro htf g n hn hpow hne
    exact absurd (htf g n hn hpow) hne

/-- The extraction package already carries torsion-freeness in its first field,
so `presented_isPowerTorsionFree_of_combMapOperations` never needed the mirror
and seam fields: the package is circular as an input. -/
theorem isPowerTorsionFree_of_extractionInputs
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (H : GirthEightTorsionExtraction.ExtractionInputs T) :
    IsPowerTorsionFree (TriangularHodgeLayer.Presented T) :=
  isPowerTorsionFree_of_cactusBaseCellDeletionForPower T H.filling

end Table

/-! ## The universal producer is false -/

/-- The one-generator triangle table `x x x`; its group is `ℤ/3`. -/
def cubeTable : Unit → TriangularHodgeLayer.Triangle Unit :=
  fun _ _ => ((), true)

/-- The generator of the `x x x` table has cube one. -/
theorem cubeTable_generator_pow_three :
    (PresentedGroup.of () : TriangularHodgeLayer.Presented cubeTable) ^ 3 = 1 := by
  have h := TriangularHodgeLayer.wordValue_triangle_eq_one cubeTable ()
  simp only [FoxBoundary.wordValue, TriangularHodgeLayer.letters_eq_three, cubeTable,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [pow_succ, pow_succ, pow_one, mul_assoc]
  exact h

/-- The character sending the generator to `1 ∈ ℤ/3` kills the relator `x x x`. -/
theorem cubeTable_character_relators :
    ∀ r ∈ (TriangularHodgeLayer.relators cubeTable : Set (FreeGroup Unit)),
      FreeGroup.lift (fun _ : Unit => Multiplicative.ofAdd (1 : ZMod 3)) r = 1 := by
  intro r hr
  have hr' : r ∈ TriangularHodgeLayer.relators cubeTable := hr
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr'
  have hw := FoxBoundary.wordValue_freeGroup_map
    (FreeGroup.lift (fun _ : Unit => Multiplicative.ofAdd (1 : ZMod 3)))
    (TriangularHodgeLayer.letters (cubeTable j))
  rw [Function.comp_apply, TriangularHodgeLayer.relator, ← hw]
  simp only [FreeGroup.lift_apply_of, FoxBoundary.wordValue,
    TriangularHodgeLayer.letters_eq_three, cubeTable, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil]
  decide

/-- The generator of the `x x x` table is not the identity. -/
theorem cubeTable_generator_ne_one :
    (PresentedGroup.of () : TriangularHodgeLayer.Presented cubeTable) ≠ 1 := by
  intro h
  have h2 := congrArg (PresentedGroup.toGroup cubeTable_character_relators) h
  rw [PresentedGroup.toGroup.of, map_one] at h2
  exact absurd h2 (by decide)

/-- **`CactusBaseCellDeletionProducer` is false.**  At the table `x x x` it would
make `ℤ/3` torsion-free. -/
theorem not_cactusBaseCellDeletionProducer :
    ¬ KazhdanHypSharpExistenceAssembly.CactusBaseCellDeletionProducer := by
  intro h
  have htf := isPowerTorsionFree_of_cactusBaseCellDeletionForPower cubeTable
    (h Unit Unit inferInstance inferInstance inferInstance inferInstance cubeTable)
  exact cubeTable_generator_ne_one
    (htf _ 3 (by norm_num) cubeTable_generator_pow_three)

end KazhdanHypCactusDeletionCounting
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.faceCount_replaceGRegion
#audit_axioms GroupApproximation.GGT.VanKampen.CactusBaseCellDeletion.replacement_innerFaceCount
#audit_axioms GroupApproximation.GGT.VanKampen.CactusBaseCellDeletion.rCellCount_add_one_le
#audit_axioms GroupApproximation.GGT.VanKampen.CactusBaseCellDeletion.listVal_boundaryWord_eq_one
#audit_axioms GroupApproximation.GGT.VanKampen.CactusBaseCellDeletion.isEmpty_of_listVal_ne_one
#audit_axioms GroupApproximation.GGT.VanKampen.listVal_replicate_flatten
#audit_axioms GroupApproximation.GGT.KazhdanHypCactusDeletionCounting.listVal_triangleRelatorWord_ne_one
#audit_axioms GroupApproximation.GGT.KazhdanHypCactusDeletionCounting.listVal_map_signedFreeRelLetter
#audit_axioms GroupApproximation.GGT.KazhdanHypCactusDeletionCounting.isPowerTorsionFree_of_cactusBaseCellDeletionForPower
#audit_axioms GroupApproximation.GGT.KazhdanHypCactusDeletionCounting.cactusBaseCellDeletionForPower_iff
#audit_axioms GroupApproximation.GGT.KazhdanHypCactusDeletionCounting.isPowerTorsionFree_of_extractionInputs
#audit_closed_axioms GroupApproximation.GGT.KazhdanHypCactusDeletionCounting.cubeTable_generator_pow_three
#audit_closed_axioms GroupApproximation.GGT.KazhdanHypCactusDeletionCounting.cubeTable_generator_ne_one
#audit_closed_axioms GroupApproximation.GGT.KazhdanHypCactusDeletionCounting.not_cactusBaseCellDeletionProducer
