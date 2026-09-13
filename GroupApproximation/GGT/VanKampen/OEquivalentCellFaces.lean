import GroupApproximation.GGT.VanKampen.RelativeGreendlinger
import GroupApproximation.Meta.AxiomGuard

/-!
# O-equivalence through relator faces

An `O`-equivalence (`OEquivalentDiscDiagram`) matches the relator cells of two diagrams by their
positions in the stored cell lists.  Surgery on a diagram is easier to describe on faces, and
this module translates between the two.

* `cellFaceEquiv Delta`: position `i` of the cell list goes to the face of the cell at `i`.  This
  is a bijection onto the relator faces.
* `OEquivalentDiscDiagram.faceEquiv` and `OEquivalentDiscDiagram.faceWord_faceEquiv`: an
  `O`-equivalence gives a bijection of relator faces preserving their words.
* `OEquivalentDiscDiagram.ofCellFaceEquiv`: the same boundary word and a word-preserving bijection
  of relator faces give an `O`-equivalence.

## Manuscript status

Infrastructure for Osin's Lemma 9.7 (arXiv:math/0411039v3, §9) through the pocket glue modules;
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}

/-- The positions of the cell list are in bijection with the relator faces: position `i` goes to
the face of the cell at `i`. -/
noncomputable def cellFaceEquiv (Delta : DiscDiagram.{u, w, v} W) :
    Fin Delta.rCellCount ≃
      {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face} :=
  Equiv.ofBijective
    (fun i => ⟨(Embedded.cell Delta i).face, List.mem_map_of_mem (Embedded.cell_mem Delta i)⟩)
    ⟨fun i j hij => by
      have hface : (Embedded.cell Delta i).face = (Embedded.cell Delta j).face :=
        congrArg Subtype.val hij
      have hi : i.1 < (Delta.relatorCells.map RelatorCell.face).length := by
        rw [List.length_map]
        exact i.2
      have hj : j.1 < (Delta.relatorCells.map RelatorCell.face).length := by
        rw [List.length_map]
        exact j.2
      have hget : (Delta.relatorCells.map RelatorCell.face)[i.1]'hi =
          (Delta.relatorCells.map RelatorCell.face)[j.1]'hj := by
        rw [List.getElem_map, List.getElem_map]
        exact hface
      exact Fin.ext (Delta.relatorCell_faces_nodup.getElem_inj_iff.mp hget),
     fun f => by
      obtain ⟨C, hC, hCf⟩ := List.mem_map.mp f.2
      obtain ⟨n, hn, hnC⟩ := List.getElem_of_mem hC
      refine ⟨⟨n, hn⟩, Subtype.ext ?_⟩
      show (Delta.relatorCells[n]'hn).face = f.1
      rw [hnC, hCf]⟩

/-- The face at a position is the face of the cell at that position. -/
theorem cellFaceEquiv_val (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount) :
    (cellFaceEquiv Delta i).1 = (Embedded.cell Delta i).face :=
  rfl

/-- The word of the face at a position is the word of the cell at that position. -/
theorem cellFaceEquiv_faceWord (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount) :
    Delta.faceWord (cellFaceEquiv Delta i).1 = (Embedded.cell Delta i).word :=
  (Delta.relatorCell_word _ (Embedded.cell_mem Delta i)).symm

namespace OEquivalentDiscDiagram

variable {Delta Delta' : DiscDiagram.{u, w, v} W}

/-- An `O`-equivalence as a bijection of relator faces. -/
noncomputable def faceEquiv (O : OEquivalentDiscDiagram Delta Delta') :
    {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face} ≃
      {f : Delta'.toCombMap.Face // f ∈ Delta'.relatorCells.map RelatorCell.face} :=
  (cellFaceEquiv Delta).symm.trans (O.cellIndex.trans (cellFaceEquiv Delta'))

/-- An `O`-equivalence carries the word of a relator face to the word of its image. -/
theorem faceWord_faceEquiv (O : OEquivalentDiscDiagram Delta Delta')
    (f : {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face}) :
    Delta'.faceWord (O.faceEquiv f).1 = Delta.faceWord f.1 := by
  show Delta'.faceWord (cellFaceEquiv Delta' (O.cellIndex ((cellFaceEquiv Delta).symm f))).1 =
    Delta.faceWord f.1
  rw [cellFaceEquiv_faceWord Delta', O.cellWord_eq, ← cellFaceEquiv_faceWord Delta,
    Equiv.apply_symm_apply]

/-- The same boundary word and a bijection of relator faces preserving their words give an
`O`-equivalence. -/
noncomputable def ofCellFaceEquiv (hbd : Delta'.boundaryWord = Delta.boundaryWord)
    (e : {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face} ≃
      {f : Delta'.toCombMap.Face // f ∈ Delta'.relatorCells.map RelatorCell.face})
    (hword : ∀ f, Delta'.faceWord (e f).1 = Delta.faceWord f.1) :
    OEquivalentDiscDiagram Delta Delta' where
  boundaryWord_eq := hbd
  cellIndex := (cellFaceEquiv Delta).trans (e.trans (cellFaceEquiv Delta').symm)
  cellWord_eq i := by
    show (Embedded.cell Delta' ((cellFaceEquiv Delta').symm (e (cellFaceEquiv Delta i)))).word =
      (Embedded.cell Delta i).word
    rw [← cellFaceEquiv_faceWord Delta', Equiv.apply_symm_apply, hword,
      cellFaceEquiv_faceWord Delta]

/-- The cell matched by `ofCellFaceEquiv` to the cell at `i` lies on the image of its face. -/
theorem ofCellFaceEquiv_face (hbd : Delta'.boundaryWord = Delta.boundaryWord)
    (e : {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face} ≃
      {f : Delta'.toCombMap.Face // f ∈ Delta'.relatorCells.map RelatorCell.face})
    (hword : ∀ f, Delta'.faceWord (e f).1 = Delta.faceWord f.1) (i : Fin Delta.rCellCount) :
    (Embedded.cell Delta' ((ofCellFaceEquiv hbd e hword).cellIndex i)).face =
      (e ⟨(Embedded.cell Delta i).face,
        List.mem_map_of_mem (Embedded.cell_mem Delta i)⟩).1 := by
  show (cellFaceEquiv Delta' ((cellFaceEquiv Delta').symm (e (cellFaceEquiv Delta i)))).1 = _
  exact congrArg Subtype.val (Equiv.apply_symm_apply (cellFaceEquiv Delta') _)

end OEquivalentDiscDiagram

#audit_axioms GroupApproximation.GGT.VanKampen.cellFaceEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.cellFaceEquiv_val
#audit_axioms GroupApproximation.GGT.VanKampen.cellFaceEquiv_faceWord
#audit_axioms GroupApproximation.GGT.VanKampen.OEquivalentDiscDiagram.faceEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.OEquivalentDiscDiagram.faceWord_faceEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.OEquivalentDiscDiagram.ofCellFaceEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.OEquivalentDiscDiagram.ofCellFaceEquiv_face

end GroupApproximation.GGT.VanKampen
