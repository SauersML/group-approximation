import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhi
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerMultigraph
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's graph `Φ'_M` with one outer vertex, subdivided

Osin, arXiv:math/0411039v3, Appendix, before Lemma 9.3: "Further let `Φ'_M` be the graph obtained
from `Φ_M` in the following way.  For each `i = 1, …, r`, we add to `Φ_M` a vertex `O_i` outside of
`∆` and for each ε-contiguity subdiagram `Γ` of a cell `Π` to `q_i`, we connect `o(Π)` to `O_i` by
an edge passing through `Γ`."

This module merges the `r` vertices `O_i` into one vertex `O`, the outer face of the collapsed
diagram (`GGT/VanKampen/Estimating/OsinAppendixEulerRegionFaces.lean`).  An end of a region is
`some i` for the relator cell `i`, or `none` for the boundary (`sideCellO`).  For a boundary target
the target arc runs along the regions' side of the outer boundary, so the dart based at `O` is the
reverse of its first dart (`crossO`).  The restriction `phiMapO family E` of the dual of the
collapsed map to these crossings is a `SubdividedMultigraph` (`phiSubdividedMultigraphO`): `Φ'_M`
with the `O_i` merged and every edge subdivided once.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

open Equiv
universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

/-- On a boundary target, every dart of the target arc lies on the boundary traversal of the face
set. -/
theorem mem_targetBoundaryDarts_of_eq_none (Delta : DiscDiagram.{u, w, v} W)
    (target : Option (Fin Delta.rCellCount)) (arc : CyclicArc (targetDarts Delta target))
    (htarget : target = none) {d : Delta.toCombMap.Dart} (hd : d ∈ arc.darts) :
    d ∈ targetBoundaryDarts Delta target arc := by
  cases target with
  | none => exact hd
  | some _ => cases htarget

/-- Crossing a dart of a boundary target arc enters the outer face. -/
theorem faceOf_alpha_of_mem_targetArc_none (Delta : DiscDiagram.{u, w, v} W)
    (target : Option (Fin Delta.rCellCount)) (arc : CyclicArc (targetDarts Delta target))
    (htarget : target = none) {d : Delta.toCombMap.Dart} (hd : d ∈ arc.darts) :
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = Delta.outerFace := by
  cases target with
  | some _ => cases htarget
  | none =>
      have hmem : d ∈ outerDarts Delta := arc.mem_cycle_of_mem_darts hd
      simp only [outerDarts, List.mem_map, List.mem_reverse] at hmem
      obtain ⟨q, hq, rfl⟩ := hmem
      rw [Delta.toCombMap.alpha_involutive]
      exact ((Delta.faceBoundary Delta.outerFace).mem_iff q).mp hq

/-- The face of an end of a region: the relator cell `i` for `some i`, the outer face for
`none`. -/
def endFace (Delta : DiscDiagram.{u, w, v} W) :
    Option (Fin Delta.rCellCount) → Delta.toCombMap.Face
  | some i => (cell Delta i).face
  | none => Delta.outerFace

theorem endFace_injective (Delta : DiscDiagram.{u, w, v} W) :
    Function.Injective (endFace Delta) := by
  intro x y h
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some j => exact ((cell Delta j).face_ne_outer h.symm).elim
  | some i =>
      cases y with
      | none => exact ((cell Delta i).face_ne_outer h).elim
      | some j =>
          have h' : (cell Delta i).face = (cell Delta j).face := h
          exact congrArg some (cell_face_injective Delta h')

namespace RegionCandidate

/-- The end of a region with one outer vertex: `true` is the source cell, `false` the target cell,
or `none` for the boundary. -/
def sideCellO (a : RegionCandidate D eps Delta) : Bool → Option (Fin Delta.rCellCount)
  | true => some a.2.source
  | false => a.2.target

/-- **The crossing darts of a region with one outer vertex.**  `cellSide = true` gives the dart
based at the end of the region (a cell, or the outer face for a boundary target), `cellSide = false`
its reverse, based inside the region. -/
noncomputable def crossO (a : RegionCandidate D eps Delta) :
    Bool → Bool → Option Delta.toCombMap.Dart
  | true, o => cross a true o
  | false, o => cross a false (a.2.target.elim (!o) fun _ => o)

theorem crossO_true (a : RegionCandidate D eps Delta) (o : Bool) :
    crossO a true o = cross a true o := rfl

theorem crossO_false_of_eq_none (a : RegionCandidate D eps Delta) (ht : a.2.target = none)
    (o : Bool) : crossO a false o = cross a false (!o) := by
  cases o <;> simp [crossO, ht]

theorem crossO_false_of_eq_some (a : RegionCandidate D eps Delta) {j : Fin Delta.rCellCount}
    (ht : a.2.target = some j) (o : Bool) : crossO a false o = cross a false o := by
  cases o <;> simp [crossO, ht]

theorem crossO_alpha (a : RegionCandidate D eps Delta) (side cellSide : Bool)
    (d : Delta.toCombMap.Dart) :
    crossO a side (!cellSide) = some (Delta.toCombMap.alpha d) ↔
      crossO a side cellSide = some d := by
  cases side with
  | true => exact cross_alpha a true cellSide d
  | false =>
      rcases Option.eq_none_or_eq_some a.2.target with ht | ⟨j, ht⟩
      · rw [crossO_false_of_eq_none a ht, crossO_false_of_eq_none a ht]
        exact cross_alpha a false (!cellSide) d
      · rw [crossO_false_of_eq_some a ht, crossO_false_of_eq_some a ht]
        exact cross_alpha a false cellSide d

theorem exists_crossO (a : RegionCandidate D eps Delta)
    (hnondeg : 0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length) (side cellSide : Bool) :
    ∃ d, crossO a side cellSide = some d := by
  cases side with
  | true => exact exists_cross a hnondeg true cellSide
  | false =>
      rcases Option.eq_none_or_eq_some a.2.target with ht | ⟨j, ht⟩
      · rw [crossO_false_of_eq_none a ht]
        exact exists_cross a hnondeg false _
      · rw [crossO_false_of_eq_some a ht]
        exact exists_cross a hnondeg false _

/-- A crossing dart at an end of a region is based at the face of that end. -/
theorem faceOf_crossO_true (a : RegionCandidate D eps Delta) {side : Bool}
    {d : Delta.toCombMap.Dart} (hd : crossO a side true = some d) :
    Delta.toCombMap.faceOf d = endFace Delta (sideCellO a side) := by
  cases side with
  | true =>
      rw [crossO_true] at hd
      simp only [cross, if_true] at hd
      exact faceOf_of_mem_cellDarts
        (a.2.sourceArc.mem_cycle_of_mem_darts (List.mem_of_mem_head? hd))
  | false =>
      rcases Option.eq_none_or_eq_some a.2.target with ht | ⟨j, ht⟩
      · rw [crossO_false_of_eq_none a ht, Bool.not_true, cross_false,
          Option.map_eq_some_iff] at hd
        obtain ⟨p, hp, rfl⟩ := hd
        simp only [cross, if_true] at hp
        have hs : sideCellO a false = none := ht
        rw [hs]
        exact faceOf_alpha_of_mem_targetArc_none Delta a.2.target a.2.targetArc ht
          (List.mem_of_mem_head? hp)
      · rw [crossO_false_of_eq_some a ht] at hd
        rw [faceOf_cross_true a (by simp [ht]) hd]
        have hs : sideCellO a false = some j := ht
        have hs' : sideCell a false = j := by simp [sideCell, ht]
        rw [hs, hs']
        rfl

/-- A crossing dart inside a region lies on the region's boundary cycle. -/
theorem mem_cycle_crossO_false (a : RegionCandidate D eps Delta) {side : Bool}
    {d : Delta.toCombMap.Dart} (hd : crossO a side false = some d) :
    d ∈ a.2.boundary.cycle := by
  cases side with
  | true =>
      rw [crossO_true, cross_false, Option.map_eq_some_iff] at hd
      obtain ⟨p, hp, rfl⟩ := hd
      simp only [cross, if_true] at hp
      have hmem : Delta.toCombMap.alpha p ∈ a.2.sourceArc.reverseDarts := by
        simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
        exact ⟨p, List.mem_of_mem_head? hp, rfl⟩
      rw [a.2.boundary_decomposition]
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hmem))
  | false =>
      rcases Option.eq_none_or_eq_some a.2.target with ht | ⟨j, ht⟩
      · rw [crossO_false_of_eq_none a ht, Bool.not_false] at hd
        simp only [cross, if_true] at hd
        rw [a.2.boundary_decomposition]
        simp only [List.mem_append]
        exact Or.inl (Or.inr (mem_targetBoundaryDarts_of_eq_none Delta a.2.target a.2.targetArc
          ht (List.mem_of_mem_head? hd)))
      · rw [crossO_false_of_eq_some a ht] at hd
        exact mem_cycle_cross_false a (by simp [ht]) hd

theorem faceOf_crossO_false (a : RegionCandidate D eps Delta) {side : Bool}
    {d : Delta.toCombMap.Dart} (hd : crossO a side false = some d) :
    Delta.toCombMap.faceOf d ∈ a.1 :=
  ((a.2.boundary.cycle_mem_iff d).mp (mem_cycle_crossO_false a hd)).1

/-- **The data of `Φ'_M` with one outer vertex**: the ambient family and the selected edges,
exterior regions included. -/
structure ExtPhiData (family E : Finset (RegionCandidate D eps Delta)) : Prop where
  subset : E ⊆ family
  pairwise : EstimatingSelection.PairwiseCompatible Compatible family
  cell_not_mem : ∀ a ∈ family, ∀ i : Fin Delta.rCellCount, (cell Delta i).face ∉ a.1
  nondegenerate : ∀ a ∈ E, 0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length
  noLoop : ∀ a ∈ E, a.2.target ≠ some a.2.source

variable {family E : Finset (RegionCandidate D eps Delta)}

/-- No region contains the face of an end. -/
theorem ExtPhiData.endFace_not_mem (P : ExtPhiData family E) (x : Option (Fin Delta.rCellCount)) :
    ∀ b ∈ family, endFace Delta x ∉ b.1 := by
  intro b hb h
  cases x with
  | none => exact (b.2.boundary.all_gCells _ h).1 rfl
  | some i => exact P.cell_not_mem b hb i h

theorem ExtPhiData.sideCellO_ne (P : ExtPhiData family E) {a : RegionCandidate D eps Delta}
    (ha : a ∈ E) : sideCellO a true ≠ sideCellO a false :=
  fun h => P.noLoop a ha h.symm

theorem ExtPhiData.face_not_mem_of_crossO_true (P : ExtPhiData family E)
    {a : RegionCandidate D eps Delta} {side : Bool} {d : Delta.toCombMap.Dart}
    (h : crossO a side true = some d) : ∀ b ∈ family, Delta.toCombMap.faceOf d ∉ b.1 := by
  intro b hb
  rw [faceOf_crossO_true a h]
  exact P.endFace_not_mem _ b hb

/-- **A crossing dart determines its region, side and orientation.** -/
theorem ExtPhiData.crossO_unique (P : ExtPhiData family E) {a b : RegionCandidate D eps Delta}
    (ha : a ∈ E) (hb : b ∈ E) {s s' o o' : Bool} {d : Delta.toCombMap.Dart}
    (h : crossO a s o = some d) (h' : crossO b s' o' = some d) : a = b ∧ s = s' ∧ o = o' := by
  have hfam : ∀ x ∈ E, x ∈ family := fun x hx => P.subset hx
  -- the orientation
  have horient : o = o' := by
    cases o with
    | true =>
        cases o' with
        | true => rfl
        | false =>
            exfalso
            exact P.face_not_mem_of_crossO_true h b (hfam b hb) (faceOf_crossO_false b h')
    | false =>
        cases o' with
        | true =>
            exfalso
            exact P.face_not_mem_of_crossO_true h' a (hfam a ha) (faceOf_crossO_false a h)
        | false => rfl
  subst horient
  -- the region
  have hregion : a = b := by
    cases o with
    | false =>
        exact eq_of_face_mem_of_face_mem P.pairwise (hfam a ha) (hfam b hb)
          (faceOf_crossO_false a h) (faceOf_crossO_false b h')
    | true =>
        have hα : crossO a s false = some (Delta.toCombMap.alpha d) :=
          (crossO_alpha a s true d).mpr h
        have hα' : crossO b s' false = some (Delta.toCombMap.alpha d) :=
          (crossO_alpha b s' true d).mpr h'
        exact eq_of_face_mem_of_face_mem P.pairwise (hfam a ha) (hfam b hb)
          (faceOf_crossO_false a hα) (faceOf_crossO_false b hα')
  subst hregion
  refine ⟨rfl, ?_, rfl⟩
  -- the side
  have hcell : ∀ t t' : Bool, ∀ x, crossO a t true = some x → crossO a t' true = some x →
      t = t' := by
    intro t t' x hx hx'
    have hidx := endFace_injective Delta
      ((faceOf_crossO_true a hx).symm.trans (faceOf_crossO_true a hx'))
    have hsc := P.sideCellO_ne ha
    cases t <;> cases t'
    · rfl
    · exact (hsc hidx.symm).elim
    · exact (hsc hidx).elim
    · rfl
  cases o with
  | true => exact hcell s s' d h h'
  | false =>
      have hy := (crossO_alpha a s true (Delta.toCombMap.alpha d)).mp
        (by rw [Bool.not_true, Delta.toCombMap.alpha_involutive]; exact h)
      have hy' := (crossO_alpha a s' true (Delta.toCombMap.alpha d)).mp
        (by rw [Bool.not_true, Delta.toCombMap.alpha_involutive]; exact h')
      exact hcell s s' _ hy hy'

/-- The retained darts of `Φ'_M` in the dual of the collapsed map. -/
def PhiKeepO (family E : Finset (RegionCandidate D eps Delta))
    (x : (collapsedMap family).Dart) : Prop :=
  ∃ a ∈ E, ∃ s o : Bool, crossO a s o = some x.1

theorem phiKeepO_alpha (x : (collapsedMap family).dual.Dart) :
    PhiKeepO family E ((collapsedMap family).dual.alpha x) ↔ PhiKeepO family E x := by
  constructor
  · rintro ⟨a, ha, s, o, h⟩
    refine ⟨a, ha, s, !o, ?_⟩
    have h' : crossO a s o = some (Delta.toCombMap.alpha x.1) := h
    have := (crossO_alpha a s (!o) x.1).mp
    rw [Bool.not_not] at this
    exact this h'
  · rintro ⟨a, ha, s, o, h⟩
    exact ⟨a, ha, s, !o, (crossO_alpha a s o x.1).mpr h⟩

/-- **Osin's `Φ'_M` with one outer vertex, subdivided**: the restriction of the dual of the
collapsed map to the crossing darts. -/
noncomputable def phiMapO (family E : Finset (RegionCandidate D eps Delta)) : CombMap.{v} :=
  CombMap.PredicateRestriction.toCombMap (collapsedMap family).dual (PhiKeepO family E)
    phiKeepO_alpha

theorem phiMapO_isRestriction (family E : Finset (RegionCandidate D eps Delta)) :
    (collapsedMap family).dual.IsRestriction (phiMapO family E)
      (Function.Embedding.subtype (PhiKeepO family E)) :=
  CombMap.PredicateRestriction.isRestriction _ _ _

/-- The region of a retained dart. -/
noncomputable def phiRegionO (y : (phiMapO family E).Dart) : RegionCandidate D eps Delta :=
  Classical.choose y.2

theorem phiRegionO_mem (y : (phiMapO family E).Dart) : phiRegionO y ∈ E :=
  (Classical.choose_spec y.2).1

/-- The side of a retained dart. -/
noncomputable def phiSideO (y : (phiMapO family E).Dart) : Bool :=
  Classical.choose (Classical.choose_spec y.2).2

/-- The orientation of a retained dart: `true` at an end, `false` at a midpoint. -/
noncomputable def phiCellSideO (y : (phiMapO family E).Dart) : Bool :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec y.2).2)

theorem phiO_cross (y : (phiMapO family E).Dart) :
    crossO (phiRegionO y) (phiSideO y) (phiCellSideO y) = some y.1.1 :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec y.2).2)

theorem ExtPhiData.phiO_eq (P : ExtPhiData family E) (y : (phiMapO family E).Dart)
    {a : RegionCandidate D eps Delta} (ha : a ∈ E) {s o : Bool} (h : crossO a s o = some y.1.1) :
    phiRegionO y = a ∧ phiSideO y = s ∧ phiCellSideO y = o :=
  P.crossO_unique (phiRegionO_mem y) ha (phiO_cross y) h

/-- The retained dart at a crossing. -/
noncomputable def phiDartO (P : ExtPhiData family E) (a : RegionCandidate D eps Delta)
    (ha : a ∈ E) (s o : Bool) : (phiMapO family E).Dart :=
  let d := Classical.choose (exists_crossO a (P.nondegenerate a ha) s o)
  have hd : crossO a s o = some d :=
    Classical.choose_spec (exists_crossO a (P.nondegenerate a ha) s o)
  have hkeep : ¬ RegionInternal family d := by
    cases o with
    | true => exact not_regionInternal_of_face_not_mem (P.face_not_mem_of_crossO_true hd)
    | false =>
        exact not_regionInternal_of_mem_cycle P.pairwise (P.subset ha)
          (mem_cycle_crossO_false a hd)
  ⟨⟨d, hkeep⟩, a, ha, s, o, hd⟩

theorem phiDartO_cross (P : ExtPhiData family E) (a : RegionCandidate D eps Delta) (ha : a ∈ E)
    (s o : Bool) : crossO a s o = some (phiDartO P a ha s o).1.1 :=
  Classical.choose_spec (exists_crossO a (P.nondegenerate a ha) s o)

theorem dartO_ext {y z : (phiMapO family E).Dart}
    (hregion : phiRegionO y = phiRegionO z) (hside : phiSideO y = phiSideO z)
    (hcell : phiCellSideO y = phiCellSideO z) : y = z := by
  have h1 := phiO_cross y
  rw [hregion, hside, hcell] at h1
  exact Subtype.ext (Subtype.ext (Option.some.inj (h1.symm.trans (phiO_cross z))))

/-- Retained darts share a vertex of `Φ'_M` exactly when they lie in one face of the collapsed
map. -/
theorem phiMapO_vertexOf_eq_iff (y z : (phiMapO family E).Dart) :
    (phiMapO family E).vertexOf y = (phiMapO family E).vertexOf z ↔
      (collapsedMap family).faceOf y.1 = (collapsedMap family).faceOf z.1 := by
  rw [(phiMapO_isRestriction family E).vertexOf_eq_iff, CombMap.vertexOf_eq_iff,
    CombMap.faceOf_eq_iff]
  rfl

variable (P : ExtPhiData family E)

/-- **`Φ'_M` with one outer vertex, subdivided, is a `SubdividedMultigraph`.**  Its ends are the
relator cells and the outer vertex `O = none`. -/
noncomputable def phiSubdividedMultigraphO :
    CombMap.SubdividedMultigraph (phiMapO family E) (RegionCandidate D eps Delta)
      (Option (Fin Delta.rCellCount)) where
  IsCellDart y := phiCellSideO y = true
  region := phiRegionO
  endCell y := sideCellO (phiRegionO y) (phiSideO y)
  cellDart_alpha y := by
    have h := (crossO_alpha (phiRegionO y) (phiSideO y) (phiCellSideO y) y.1.1).mpr (phiO_cross y)
    obtain ⟨-, -, hcell⟩ := P.phiO_eq ((phiMapO family E).alpha y) (phiRegionO_mem y) h
    rw [hcell]
    cases phiCellSideO y <;> simp
  region_alpha y := by
    have h := (crossO_alpha (phiRegionO y) (phiSideO y) (phiCellSideO y) y.1.1).mpr (phiO_cross y)
    exact (P.phiO_eq ((phiMapO family E).alpha y) (phiRegionO_mem y) h).1
  endCell_alpha y := by
    have h := (crossO_alpha (phiRegionO y) (phiSideO y) (phiCellSideO y) y.1.1).mpr (phiO_cross y)
    obtain ⟨hr, hs, -⟩ := P.phiO_eq ((phiMapO family E).alpha y) (phiRegionO_mem y) h
    simp only [hr, hs]
  cellDart_of_vertex y z hyz := by
    rw [phiMapO_vertexOf_eq_iff] at hyz
    -- an end dart and a midpoint dart never share a face of the collapsed map
    have hcase : ∀ (p q : (phiMapO family E).Dart), phiCellSideO p = true →
        phiCellSideO q = false →
        (collapsedMap family).faceOf p.1 = (collapsedMap family).faceOf q.1 → False := by
      intro p q hp hq hpq
      have hpc := phiO_cross p
      rw [hp] at hpc
      have hqc := phiO_cross q
      rw [hq] at hqc
      have hface := P.face_not_mem_of_crossO_true hpc
      have hq_face := collapsed_faceOf_eq_imp_face_eq hface q.1 hpq.symm
      have hmem := faceOf_crossO_false (phiRegionO q) hqc
      rw [hq_face] at hmem
      exact hface (phiRegionO q) (P.subset (phiRegionO_mem q)) hmem
    cases hy : phiCellSideO y <;> cases hz : phiCellSideO z
    · simp
    · exact (hcase z y hz hy hyz.symm).elim
    · exact (hcase y z hy hz hyz).elim
    · simp
  endCell_of_vertex y z hy hz hyz := by
    rw [phiMapO_vertexOf_eq_iff] at hyz
    have hyc := phiO_cross y
    rw [show phiCellSideO y = true from hy] at hyc
    have hzc := phiO_cross z
    rw [show phiCellSideO z = true from hz] at hzc
    have hface := P.face_not_mem_of_crossO_true hyc
    have hzf := collapsed_faceOf_eq_imp_face_eq hface z.1 hyz.symm
    have hf := faceOf_crossO_true (phiRegionO y) hyc
    have hf' := faceOf_crossO_true (phiRegionO z) hzc
    exact endFace_injective Delta (hf.symm.trans (hzf.symm.trans hf'))
  region_of_vertex y z hy hz hyz := by
    rw [phiMapO_vertexOf_eq_iff] at hyz
    have hyc := phiO_cross y
    rw [show phiCellSideO y = false by simpa using hy] at hyc
    have hzc := phiO_cross z
    rw [show phiCellSideO z = false by simpa using hz] at hzc
    have hymem := mem_cycle_crossO_false (phiRegionO y) hyc
    have hzmem := mem_cycle_of_collapsed_faceOf_eq P.pairwise (P.subset (phiRegionO_mem y))
      hymem z.1 hyz.symm
    have hzface : Delta.toCombMap.faceOf z.1.1 ∈ (phiRegionO y).1 :=
      (((phiRegionO y).2.boundary.cycle_mem_iff _).mp hzmem).1
    exact eq_of_face_mem_of_face_mem P.pairwise (P.subset (phiRegionO_mem y))
      (P.subset (phiRegionO_mem z)) hzface (faceOf_crossO_false (phiRegionO z) hzc)
  sigma_ne_of_midpoint y hy := by
    have hyc := phiO_cross y
    rw [show phiCellSideO y = false by simpa using hy] at hyc
    have hzc := phiDartO_cross P (phiRegionO y) (phiRegionO_mem y) (!phiSideO y) false
    have hzside : phiSideO (phiDartO P (phiRegionO y) (phiRegionO_mem y) (!phiSideO y) false) =
        !phiSideO y :=
      (P.phiO_eq _ (phiRegionO_mem y) hzc).2.1
    have hzy : phiDartO P (phiRegionO y) (phiRegionO_mem y) (!phiSideO y) false ≠ y := by
      intro h
      rw [h] at hzside
      cases hs : phiSideO y <;> simp [hs] at hzside
    have hymem := mem_cycle_crossO_false (phiRegionO y) hyc
    have hzmem := mem_cycle_crossO_false (phiRegionO y) hzc
    have hface := collapsed_faceOf_eq_of_mem_cycle P.pairwise (P.subset (phiRegionO_mem y))
      hymem hzmem
    have hcycle : (collapsedMap family).dual.sigma.SameCycle
        ((Function.Embedding.subtype (PhiKeepO family E)) y)
        ((Function.Embedding.subtype (PhiKeepO family E))
          (phiDartO P (phiRegionO y) (phiRegionO_mem y) (!phiSideO y) false)) :=
      ((collapsedMap family).faceOf_eq_iff _ _).mp hface
    exact PermFirstReturn.apply_ne_self_of_sameCycle
      (CombMap.PredicateRestriction.sigma_firstReturn (collapsedMap family).dual
        (PhiKeepO family E))
      hzy hcycle
  endCell_ne y z hy hz hregion hne := by
    have hyo : phiCellSideO y = false := by simpa using hy
    have hzo : phiCellSideO z = false := by simpa using hz
    have hside : phiSideO y ≠ phiSideO z :=
      fun hs => hne (dartO_ext hregion.symm hs (hyo.trans hzo.symm))
    have hsc := P.sideCellO_ne (phiRegionO_mem y)
    change sideCellO (phiRegionO y) (phiSideO y) ≠ sideCellO (phiRegionO z) (phiSideO z)
    rw [hregion]
    intro heq
    cases hsy : phiSideO y <;> cases hsz : phiSideO z
    · exact hside (hsy.trans hsz.symm)
    · rw [hsy, hsz] at heq
      exact hsc heq.symm
    · rw [hsy, hsz] at heq
      exact hsc heq
    · exact hside (hsy.trans hsz.symm)
  midpoint_two d e x hd he hx hed hxd hde := by
    have hdo : phiCellSideO d = false := by simpa using hd
    have heo : phiCellSideO e = false := by simpa using he
    have hxo : phiCellSideO x = false := by simpa using hx
    have hside : phiSideO d ≠ phiSideO e :=
      fun hs => hde (dartO_ext hed.symm hs (hdo.trans heo.symm))
    by_cases hxs : phiSideO x = phiSideO d
    · exact Or.inl (dartO_ext hxd hxs (hxo.trans hdo.symm))
    · refine Or.inr (dartO_ext (hxd.trans hed.symm) ?_ (hxo.trans heo.symm))
      revert hxs hside
      cases phiSideO x <;> cases phiSideO d <;> cases phiSideO e <;> decide

end RegionCandidate
end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.endFace_injective
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.exists_crossO
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.crossO_unique
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.phiSubdividedMultigraphO
