import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegion
import GroupApproximation.GGT.VanKampen.SurgeryInnerCollapse
import GroupApproximation.Meta.AxiomGuard

/-!
# The boundary value of a pocket region with no relator cell

Osin, arXiv:math/0411039v3, §9, proofs of Lemmas 9.3 and 9.7: a pocket of the diagram that
contains no R-cell is merged into one G-cell.  The merge (`Surgery.InnerGRegion.diagram`) needs
the boundary cycle of the pocket to read the identity of `G`.  This file supplies that value
with no shelling.

The pocket as a van Kampen diagram (`PocketRegion.diagram`) has at most as many relator cells
as `Δ` has inside the face set (`PocketRegion.diagram_rCellCount_le`), so it has none.  Its
boundary value is then the empty product, a relator product with budget `0`, and
`PocketRegion.isRelatorProduct_inner_of_diagram` moves that budget onto the boundary cycle of
the face set.  A relator product with budget `0` is the identity.

* `PocketRegion.diagram_relatorCells_eq_nil`: the pocket has no relator cell.
* `PocketRegion.isRelatorProduct_zero_inner`: the word on the boundary cycle of the face set is
  a relator product with budget `0`.
* `PocketRegion.listVal_inner_eq_one`: that word reads the identity.
* `PocketRegion.listVal_eq_one_of_isRotated`: so does the word on every cyclic permutation of
  the cycle, for instance the cycle of an embedded boundary started at another dart.
* `Surgery.InnerGRegion.ofPocketRegion`: an embedded boundary of the face set whose cycle is a
  cyclic permutation of the pocket cycle gives an inner G-region.  Its `value_one` comes from
  the above, not from `InnerGRegion.ofShelling`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}

namespace PocketRegion

variable {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}

/-- **A pocket with no relator cell among its faces has no relator cell as a diagram.** -/
theorem diagram_relatorCells_eq_nil (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces) :
    P.diagram.relatorCells = [] := by
  have hcount : P.diagram.rCellCount = 0 := by
    refine Nat.le_zero.mp (P.diagram_rCellCount_le.trans (le_of_eq ?_))
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro C hC
    simpa using hcells C hC
  exact List.length_eq_zero_iff.mp hcount

/-- **The boundary word of a pocket with no relator cell is a relator product with budget
`0`.** -/
theorem isRelatorProduct_zero_inner (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces) (R : Set G) :
    RelatorDefectBudget.IsRelatorProduct R 0
      (RelLetter.listVal (Embedded.dartWord Delta P.inner.cycle)) := by
  apply P.isRelatorProduct_inner_of_diagram
  rw [P.diagram.boundaryValue_eq_one_of_no_rCells (P.diagram_relatorCells_eq_nil hcells)]
  exact RelatorDefectBudget.IsRelatorProduct.one

/-- **A pocket with no relator cell reads the identity along its boundary cycle.** -/
theorem listVal_inner_eq_one (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces) :
    RelLetter.listVal (Embedded.dartWord Delta P.inner.cycle) = 1 :=
  (P.isRelatorProduct_zero_inner hcells (RelLetter.listVal '' W)).eq_one_of_index_zero

/-- **Every cyclic permutation of the boundary cycle of a pocket with no relator cell reads the
identity.** -/
theorem listVal_eq_one_of_isRotated (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces) {l : List Delta.toCombMap.Dart}
    (hl : l ~r P.inner.cycle) :
    RelLetter.listVal (Embedded.dartWord Delta l) = 1 := by
  obtain ⟨n, hn⟩ := hl
  have hword : Embedded.dartWord Delta P.inner.cycle =
      (Embedded.dartWord Delta l).rotate n := by
    rw [← hn]
    exact List.map_rotate Delta.label l n
  have h := P.isRelatorProduct_zero_inner hcells (RelLetter.listVal '' W)
  rw [hword] at h
  exact (isRelatorProduct_listVal_of_rotate _ n h).eq_one_of_index_zero

end PocketRegion

namespace Surgery.InnerGRegion

variable {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}

/-- **A pocket with no relator cell and an embedded boundary is an inner G-region.**  The
boundary cycle may start at any dart of the pocket cycle; the boundary value comes from
`PocketRegion.listVal_eq_one_of_isRotated`, not from a shelling. -/
def ofPocketRegion (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces)
    (boundary : Embedded.FaceSetBoundary Delta P.faces)
    (hrot : boundary.cycle ~r P.inner.cycle) : InnerGRegion Delta where
  faces := P.faces
  boundary := boundary
  cells_avoid := hcells
  value_one := P.listVal_eq_one_of_isRotated hcells hrot

theorem ofPocketRegion_faces (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces)
    (boundary : Embedded.FaceSetBoundary Delta P.faces)
    (hrot : boundary.cycle ~r P.inner.cycle) :
    (ofPocketRegion P hcells boundary hrot).faces = P.faces :=
  rfl

theorem ofPocketRegion_boundary_cycle (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces)
    (boundary : Embedded.FaceSetBoundary Delta P.faces)
    (hrot : boundary.cycle ~r P.inner.cycle) :
    (ofPocketRegion P hcells boundary hrot).boundary.cycle = boundary.cycle :=
  rfl

end Surgery.InnerGRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.diagram_relatorCells_eq_nil
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.isRelatorProduct_zero_inner
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.listVal_inner_eq_one
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.listVal_eq_one_of_isRotated
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.ofPocketRegion
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.ofPocketRegion_faces
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.ofPocketRegion_boundary_cycle
