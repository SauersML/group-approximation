import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.Hole
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PlanarPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94RegionSideCount
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PinchedQuadrilateral
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhi
import GroupApproximation.GGT.VanKampen.Estimating.ContiguityGeometry
import GroupApproximation.GGT.VanKampen.SurgeryCellHairThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# A hole region meets no selected region

A hole region `E` (module `Hole`) holds no relator cell and not the outer face, and is closed
under reversal off the cell `C`.  A selected region with a boundary dart on `E` has its whole
boundary cycle on `E` (the boundary steps cross only faces of the region, none of them a relator
face); its source arc then lies on `C`, and so does its target arc, against `target ≠ source`.

Consequence (`region_fact`): across a dart of the polygon face lying on `E` is the polygon face
itself or `C`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue

open Equiv GroupApproximation.GGT.VanKampen.Embedded SimpleClosedWalkSides FirstTurnEnclosure
open scoped Classical

universe u w v

/-- The four side classes, as a disjunction. -/
theorem sideClass_cases {n : ℕ} (x : OsinLemma94SideClass n) :
    (∃ i, x = .cell i) ∨ (∃ i, x = .boundary i) ∨ x = .cutting ∨ x = .short := by
  cases x with
  | cell i => exact Or.inl ⟨i, rfl⟩
  | boundary i => exact Or.inr (Or.inl ⟨i, rfl⟩)
  | cutting => exact Or.inr (Or.inr (Or.inl rfl))
  | short => exact Or.inr (Or.inr (Or.inr rfl))

/-- A property propagated along a closed chain holds everywhere once it holds somewhere. -/
theorem chain_forall {α : Type*} {R : α → α → Prop} {Q : α → Prop} {l : List α} (hl : l ≠ [])
    (hchain : l.IsChain R) (hclose : R (l.getLast hl) (l.head hl))
    (hR : ∀ x y, R x y → Q x → Q y) {x : α} (hx : x ∈ l) (hQ : Q x) : ∀ y ∈ l, Q y := by
  have hstep : ∀ (i : ℕ) (h : i + 1 < l.length), Q l[i] → Q l[i + 1] := fun i h =>
    hR _ _ (hchain.getElem i h)
  have hforward : ∀ (i : ℕ) (_hi : i < l.length), Q l[i] →
      ∀ (i' : ℕ) (_hi' : i' < l.length), i ≤ i' → Q l[i'] := by
    intro i _hi hQi i'
    induction i' with
    | zero =>
      intro _hi' hle
      have h0 : i = 0 := by omega
      subst h0
      exact hQi
    | succ i' ih =>
      intro hi' hle
      by_cases h : i = i' + 1
      · subst h
        exact hQi
      · exact hstep i' hi' (ih (by omega) (by omega))
  have hlen : 0 < l.length := List.length_pos_iff.mpr hl
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hlast : Q (l.getLast hl) := by
    rw [List.getLast_eq_getElem hl]
    exact hforward i hi hQ (l.length - 1) (by omega) (by omega)
  have hhead : Q l[0] := by
    have h := hR _ _ hclose hlast
    rwa [List.head_eq_getElem hl] at h
  intro y hy
  obtain ⟨i', hi', rfl⟩ := List.mem_iff_getElem.mp hy
  exact hforward 0 hlen hhead i' hi' (Nat.zero_le _)

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- A boundary step of a selected region keeps a hole region. -/
theorem mem_of_boundaryStep {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
    (hvalue : ∀ C ∈ X.relatorCells, RelLetter.listVal C.word ≠ 1)
    {f : X.toCombMap.Face} {j : Fin X.rCellCount} {E : Finset X.toCombMap.Face}
    (hH : HoleRegion X f (cell X j).face E) (a : RegionCandidate D eps X)
    {d e : X.toCombMap.Dart} (hstep : BoundaryStep X a.1 d e)
    (hd : X.toCombMap.faceOf d ∈ E) : X.toCombMap.faceOf e ∈ E := by
  obtain ⟨_, _, hrt⟩ := hstep
  have hfp : X.toCombMap.faceOf (X.toCombMap.facePerm d) ∈ E := by
    rw [X.toCombMap.faceOf_facePerm]
    exact hd
  induction hrt with
  | refl => exact hfp
  | tail _ hmove ih =>
    obtain ⟨_, hα, rfl⟩ := hmove
    rw [X.toCombMap.faceOf_facePerm]
    refine hH.2.2.2.2 _ ih fun h => ?_
    rw [h] at hα
    exact CellHairThickening.relatorFace_not_mem hvalue (cell_mem X j) a hα

section Family

variable {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- An arc dart of a relator cell whose reverse lies on a hole region lies on `C`. -/
theorem cell_eq_of_alpha_mem {f : S.diagram.toCombMap.Face} {j i : Fin S.diagram.rCellCount}
    {E : Finset S.diagram.toCombMap.Face}
    (hH : HoleRegion S.diagram f (cell S.diagram j).face E) {d : S.diagram.toCombMap.Dart}
    (hd : d ∈ cellDarts S.diagram i)
    (hαE : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ E) : i = j := by
  by_contra hij
  have hne : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
      (S.diagram.toCombMap.alpha d)) ≠ (cell S.diagram j).face := by
    rw [S.diagram.toCombMap.alpha_involutive d, faceOf_of_mem_cellDarts hd]
    exact fun h => hij (cell_face_injective S.diagram h)
  have hmem := hH.2.2.2.2 _ hαE hne
  rw [S.diagram.toCombMap.alpha_involutive d, faceOf_of_mem_cellDarts hd] at hmem
  exact hH.2.2.2.1 _ (cell_mem S.diagram i) hmem

/-- **No selected region has a boundary dart on a hole region.** -/
theorem region_false (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    {f : S.diagram.toCombMap.Face} {j : Fin S.diagram.rCellCount}
    {E : Finset S.diagram.toCombMap.Face}
    (hH : HoleRegion S.diagram f (cell S.diagram j).face E)
    {a : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) {x : S.diagram.toCombMap.Dart}
    (hx : IsBoundaryDart S.diagram a.1 x) (hxE : S.diagram.toCombMap.faceOf x ∈ E) : False := by
  have hall : ∀ y ∈ a.2.boundary.cycle, S.diagram.toCombMap.faceOf y ∈ E :=
    chain_forall (Q := fun y => S.diagram.toCombMap.faceOf y ∈ E) a.2.boundary.cycle_nonempty
      a.2.boundary.cycle_chain a.2.boundary.cycle_closes
      (fun _ _ hstep hd => mem_of_boundaryStep hvalue hH a hstep hd)
      ((a.2.boundary.cycle_mem_iff x).mpr hx) hxE
  -- The source arc lies on `C`.
  have hsne : a.2.sourceArc.darts ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [a.2.sourceArc.darts_length]
    exact (S.nondegenerate a ha).1
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hsne
  have hdcell : d ∈ cellDarts S.diagram a.2.source := a.2.sourceArc.mem_cycle_of_mem_darts hd
  have hαd : S.diagram.toCombMap.alpha d ∈ a.2.boundary.cycle := by
    rw [a.2.boundary_decomposition]
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
    show S.diagram.toCombMap.alpha d ∈
      a.2.sourceArc.darts.reverse.map S.diagram.toCombMap.alpha
    exact List.mem_map_of_mem (List.mem_reverse.mpr hd)
  have hsource : a.2.source = j := cell_eq_of_alpha_mem (S := S) hH hdcell (hall _ hαd)
  -- The target arc lies on `C` as well.
  have htne := targetBoundaryDarts_ne_nil_of_length_pos a.2.targetArc (S.nondegenerate a ha).2
  obtain ⟨x', hx'⟩ := List.exists_mem_of_ne_nil _ htne
  have hcyc' : x' ∈ a.2.boundary.cycle := by
    rw [a.2.boundary_decomposition]
    exact List.mem_append_left _ (List.mem_append_right _ hx')
  rcases mem_targetBoundaryDarts_cases S.diagram a.2.target a.2.targetArc hx' with
    ⟨_, hout⟩ | ⟨i, hi, e, he, rfl⟩
  · simp only [outerDarts, List.mem_map, List.mem_reverse] at hout
    obtain ⟨e, he, rfl⟩ := hout
    have he' : S.diagram.toCombMap.faceOf e = S.diagram.outerFace :=
      ((S.diagram.faceBoundary S.diagram.outerFace).mem_iff e).mp he
    have hne : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
        (S.diagram.toCombMap.alpha e)) ≠ (cell S.diagram j).face := by
      rw [S.diagram.toCombMap.alpha_involutive e, he']
      exact fun h => (cell S.diagram j).face_ne_outer h.symm
    have hmem := hH.2.2.2.2 _ (hall _ hcyc') hne
    rw [S.diagram.toCombMap.alpha_involutive e, he'] at hmem
    exact hH.2.2.1 hmem
  · have hecell : e ∈ targetDarts S.diagram a.2.target := a.2.targetArc.mem_cycle_of_mem_darts he
    rw [hi] at hecell
    have hecell' : e ∈ cellDarts S.diagram i := hecell
    have hij : i = j := cell_eq_of_alpha_mem (S := S) hH hecell' (hall _ hcyc')
    exact (S.respects a ha).1 (by rw [hi, hij, hsource])

/-- **Across a polygon dart on a hole region**: the polygon face or `C`. -/
theorem region_fact (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {j : Fin S.diagram.rCellCount}
    {E : Finset S.diagram.toCombMap.Face}
    (hH : HoleRegion S.diagram (P.face k) (cell S.diagram j).face E)
    {y : S.diagram.toCombMap.Dart} (hy : S.diagram.toCombMap.faceOf y = P.face k) :
    S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha y) = P.face k ∨
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha y) = (cell S.diagram j).face := by
  by_cases hC : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha y) = (cell S.diagram j).face
  · exact Or.inr hC
  have hαE : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha y) ∈ E :=
    hH.2.2.2.2 y (by rw [hy]; exact hH.1) hC
  have hwalk : y ∈ (List.range (P.sideCount k)).flatMap (P.sideDarts k) := by
    rw [← P.walk k]
    exact List.mem_rotate.mpr (((S.diagram.faceBoundary (P.face k)).mem_iff y).mpr hy)
  obtain ⟨i, hi, hyi⟩ := List.mem_flatMap.mp hwalk
  have hi' : i < P.sideCount k := List.mem_range.mp hi
  rcases sideClass_cases (P.kind k i) with ⟨j', hj'⟩ | ⟨j', hj'⟩ | hcut | hshort
  · obtain ⟨arc, harc⟩ := P.cell_arc k i j' hi' hj'
    rw [harc] at hyi
    have hyi' : y ∈ arc.darts.reverse.map S.diagram.toCombMap.alpha := hyi
    simp only [List.mem_map, List.mem_reverse] at hyi'
    obtain ⟨e, he, rfl⟩ := hyi'
    have hecell : e ∈ cellDarts S.diagram j' := arc.mem_cycle_of_mem_darts he
    rw [S.diagram.toCombMap.alpha_involutive e, faceOf_of_mem_cellDarts hecell] at hαE
    exact (hH.2.2.2.1 _ (cell_mem S.diagram j') hαE).elim
  · obtain ⟨_, arc, harc, _⟩ := P.boundary_arc k i j' hi' hj'
    rw [harc] at hyi
    have hout : y ∈ outerDarts S.diagram := arc.mem_cycle_of_mem_darts hyi
    simp only [outerDarts, List.mem_map, List.mem_reverse] at hout
    obtain ⟨e, he, rfl⟩ := hout
    have he' : S.diagram.toCombMap.faceOf e = S.diagram.outerFace :=
      ((S.diagram.faceBoundary S.diagram.outerFace).mem_iff e).mp he
    rw [S.diagram.toCombMap.alpha_involutive e, he'] at hαE
    exact (hH.2.2.1 hαE).elim
  · exact Or.inl (P.cutting_internal k i hi' hcut y hyi)
  · obtain ⟨a, ha, hsa⟩ := P.short_region k i hi' hshort
    have hbd : IsBoundaryDart S.diagram a.1 (S.diagram.toCombMap.alpha y) := by
      refine ⟨hsa y hyi, ?_⟩
      rw [S.diagram.toCombMap.alpha_involutive y, hy]
      exact P.face_unselected k a ha
    exact (region_false hvalue hH ha hbd hαE).elim

end Family

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue
