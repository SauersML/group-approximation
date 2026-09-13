import GroupApproximation.GGT.VanKampen.SurgeryCellHairThickeningSides
import GroupApproximation.GGT.VanKampen.SurgeryOuterSideThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# Cell hair thickening keeping the side conditions

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The copy satisfying the edge conditions
`PocketWalk.CopyClean` is built by thickenings in this order: `OuterSideThickening` (no outer
side dart, which gives `side_outer`), `CellSideThickening` (no cell-side dart, which gives
`side_cell`), and last `CellHairThickening` (no cell hair, which gives `cell_self`).  The last one
must keep what the earlier ones produced.

Opening a relator face along a dart keeps the exterior traversal, and every region keeps its
sides through `embed`.  So an outer side dart of the doubled diagram is the image of an old one
(`noOuterSideDart`), as is a cell-side dart (`noCellSideDart`, `SurgeryCellHairThickeningSides`).

* `noOuterSideDart`.
* `exists_cellHairFree_sides`: `exists_cellHairFree`, also keeping both side conditions.
* `CellHairSidesThickeningStatement`, `cellHairSidesThickening`: from a distinguished family with
  no outer spur, no outer cell dart, no outer side dart, no cell-side dart and no relator word of
  value one, a family over the same cuts on an O-equivalent diagram with all five and no cell hair.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CellHairThickening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

universe u w v

section Sides

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-- **Opening a relator face along a dart creates no outer side dart.** -/
theorem noOuterSideDart {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∉ a.1)
    (hfree : ∀ x, ¬ OuterSideThickening.IsOuterSideDart Delta family x) :
    ∀ x, ¬ OuterSideThickening.IsOuterSideDart (FaceEdgeDoubling.diagram Delta f j hlen hf)
      (FaceEdgeDoubling.regionFamily Delta f j hlen hf family havoid) x := by
  intro x hx
  obtain ⟨hout, a, ha, hax⟩ := hx
  obtain ⟨d, hd, hdx⟩ := exists_of_faceOf_eq_outer Delta f j hlen hf hout
  subst hdx
  obtain ⟨b, hb, e, he, hex⟩ := exists_of_mem_sides Delta f j hlen hf family havoid ha hax
  change embed Delta.toCombMap e = embed Delta.toCombMap (Delta.toCombMap.alpha d) at hex
  have hea : e = Delta.toCombMap.alpha d := embed_injective Delta.toCombMap hex
  subst hea
  exact hfree d ⟨hd, b, hb, he⟩

end Sides

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **Induction on the number of cell hairs**, keeping the absence of outer spurs, outer cell
darts, outer side darts, cell-side darts and relator words of value one. -/
theorem exists_cellHairFree_sides
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hspur : ∀ x, ¬ OuterSpurThickening.IsOuterSpur S.diagram x)
    (hcell : ∀ x, ¬ OuterCellThickening.IsOuterCellDart S.diagram x)
    (hoside : ∀ x, ¬ OuterSideThickening.IsOuterSideDart S.diagram S.family x)
    (hcside : ∀ x, ¬ CellSideThickening.IsCellSideDart S.diagram S.family x) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ OuterSpurThickening.IsOuterSpur S'.diagram x) ∧
          (∀ x, ¬ OuterCellThickening.IsOuterCellDart S'.diagram x) ∧
            (∀ x, ¬ OuterSideThickening.IsOuterSideDart S'.diagram S'.family x) ∧
              (∀ x, ¬ CellSideThickening.IsCellSideDart S'.diagram S'.family x) ∧
                (∀ x, ¬ IsCellHair S'.diagram x) ∧
                  (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
                    S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
                      ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                        (e a).1.2.source.val = a.1.2.source.val := by
  revert hvalue hspur hcell hoside hcside
  generalize hn : cellHairCount S.diagram = n
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    intro hvalue hspur hcell hoside hcside
    by_cases hhair : ∃ x, IsCellHair S.diagram x
    · obtain ⟨x, hx⟩ := hhair
      obtain ⟨j, hj⟩ := HairOpening.exists_dart_eq x
      have hlen := HairOpening.one_lt_length_of_isHair hx.1
      have hh : S.diagram.toCombMap.faceOf x =
          S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) := hx.1
      obtain ⟨C, hC, hCf⟩ := hx.2
      have hf : S.diagram.toCombMap.faceOf x ≠ S.diagram.outerFace := by
        rw [← hCf]
        exact C.face_ne_outer
      have hcell2 :
          IsCellHair S.diagram (FaceEdgeDoubling.dart S.diagram (S.diagram.toCombMap.faceOf x) j) := by
        rw [hj]
        exact hx
      have havoid : ∀ a ∈ S.family, S.diagram.toCombMap.faceOf x ∉ a.1 ∧
          S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
            (FaceEdgeDoubling.dart S.diagram (S.diagram.toCombMap.faceOf x) j)) ∉ a.1 := by
        intro a _
        have hnot := relatorFace_not_mem hvalue hC a
        rw [hCf] at hnot
        refine ⟨hnot, ?_⟩
        rw [hj, ← hh]
        exact hnot
      obtain ⟨S', e, ⟨equiv'⟩, hspur', hcell', hoside', hcside', hhair', hvalue', hweight,
          hprofile⟩ :=
        ih _ (lt_of_lt_of_eq (cellHairCount_lt S.diagram _ j hlen hf hcell2) hn)
          (HairOpening.sectionFamily S _ j hlen hf havoid) rfl
          (relatorValue_ne_one S.diagram _ j hlen hf hvalue)
          (noOuterSpur S.diagram _ j hlen hf hspur)
          (noOuterCellDart S.diagram _ j hlen hf hcell)
          (noOuterSideDart S.diagram _ j hlen hf S.family havoid hoside)
          (noCellSideDart S.diagram _ j hlen hf S.family havoid hvalue hcside)
      refine ⟨S', (HairOpening.regionFamilyEquiv S.diagram _ j hlen hf S.family havoid).trans e,
        ⟨(FaceEdgeDoubling.oEquivalent S.diagram _ j hlen hf).trans equiv'⟩, hspur', hcell',
        hoside', hcside', hhair', hvalue',
        hweight.trans (FaceEdgeDoubling.regionFamily_weight S.diagram _ j hlen hf S.family havoid),
        fun a => ?_⟩
      obtain ⟨hprof, hsource⟩ :=
        hprofile (HairOpening.regionFamilyEquiv S.diagram _ j hlen hf S.family havoid a)
      exact And.intro
        (hprof.trans
          (HairOpening.regionFamilyEquiv_profile S.diagram _ j hlen hf S.family havoid a))
        (hsource.trans
          (HairOpening.regionFamilyEquiv_source S.diagram _ j hlen hf S.family havoid a))
    · exact ⟨S, Equiv.refl _, ⟨OEquivalentDiscDiagram.refl _⟩, hspur, hcell, hoside, hcside,
        fun x hx => hhair ⟨x, hx⟩, hvalue, rfl,
        fun _ => And.intro (And.intro Iff.rfl (And.intro rfl (And.intro rfl rfl))) rfl⟩

end Family

/-- **Cell hair thickening, keeping the side conditions.**  A distinguished section family over
a boundary word of length at least two whose diagram has no relator word of value one, no outer
spur, no edge between a relator cell and the exterior, no outer side dart and no cell-side dart
has a distinguished section family over the same cuts whose diagram is O-equivalent to the old
one, keeps all five properties, and has no edge with one relator cell on both sides.  Its regions
correspond bijectively to the old ones, with the same total weight, and every region keeps its
target profile and the index of its source cell. -/
def CellHairSidesThickeningStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    1 < Delta.boundaryWord.length →
      (∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) →
        (∀ x, ¬ OuterSpurThickening.IsOuterSpur S.diagram x) →
          (∀ x, ¬ OuterCellThickening.IsOuterCellDart S.diagram x) →
            (∀ x, ¬ OuterSideThickening.IsOuterSideDart S.diagram S.family x) →
              (∀ x, ¬ CellSideThickening.IsCellSideDart S.diagram S.family x) →
                ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
                  (e : S.family ≃ S'.family),
                  Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
                    (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
                      (∀ x, ¬ OuterSpurThickening.IsOuterSpur S'.diagram x) ∧
                        (∀ x, ¬ OuterCellThickening.IsOuterCellDart S'.diagram x) ∧
                          (∀ x, ¬ OuterSideThickening.IsOuterSideDart S'.diagram S'.family x) ∧
                            (∀ x, ¬ CellSideThickening.IsCellSideDart S'.diagram S'.family x) ∧
                              (∀ x, ¬ IsCellHair S'.diagram x) ∧
                                S'.toRealizedSectionFamily.weight =
                                    S.toRealizedSectionFamily.weight ∧
                                  ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                                    (e a).1.2.source.val = a.1.2.source.val

theorem cellHairSidesThickening : CellHairSidesThickeningStatement.{u, w, v} := by
  unfold CellHairSidesThickeningStatement
  intro _ _ _ D lambda c eps W Delta cuts S _ hvalue hspur hcell hoside hcside
  obtain ⟨S', e, hequiv, hspur', hcell', hoside', hcside', hhair', hvalue', hweight, hprofile⟩ :=
    exists_cellHairFree_sides S hvalue hspur hcell hoside hcside
  exact ⟨S', e, hequiv, hvalue', hspur', hcell', hoside', hcside', hhair', hweight, hprofile⟩

end GroupApproximation.GGT.VanKampen.CellHairThickening

#audit_closed_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.cellHairSidesThickening
#audit_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.noOuterSideDart
#audit_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.exists_cellHairFree_sides
