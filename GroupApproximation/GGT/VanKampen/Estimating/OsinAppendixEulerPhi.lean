import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerRegionFaces
import GroupApproximation.GGT.VanKampen.CombMapDual
import GroupApproximation.GGT.VanKampen.CombMapEdgeInsertion
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's graph `Φ_M` as a subdivided planar map

Let `family` be a pairwise compatible family of contiguity regions of a disc diagram, no region
containing a relator cell, and let `E ⊆ family` be interior regions whose two arcs are nonempty, with
no loops and no two regions joining the same cells.  In the dual of the collapsed diagram
(`GGT/VanKampen/Estimating/OsinAppendixEulerRegionFaces.lean`) a cell is a vertex and a region is a
vertex, its midpoint.  Keep, for each region, the dart crossing the first dart of its source arc and
the dart crossing the first dart of its target arc (`RegionCandidate.cross`), with their reverses.
The resulting restriction `phiMap family E` is a `SubdividedGraph` (`phiSubdividedGraph`): Osin's
graph `Φ_M` with every edge subdivided once.  It has `4|E|` darts (`phiMap_dartCount`), at most
`|V| + |E|` vertices for any cell set `V` containing the endpoints (`phiMap_vertexCount_le`), and is
connected when the regions are linked through shared cells (`phiMap_connected`).  Euler's count of
`GGT/VanKampen/Estimating/OsinAppendixEulerSubdivided.lean` then gives `|E| ≤ 3(|V| − 1)`
(`card_le_of_linked`).
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

open Equiv
universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

/-- Distinct relator-cell indices have distinct faces. -/
theorem cell_face_injective (Delta : DiscDiagram.{u, w, v} W) :
    Function.Injective fun i : Fin Delta.rCellCount => (cell Delta i).face := by
  intro i j h
  have hnodup := Delta.relatorCell_faces_nodup
  have hi : i.1 < (Delta.relatorCells.map RelatorCell.face).length := by
    rw [List.length_map]
    exact i.2
  have hj : j.1 < (Delta.relatorCells.map RelatorCell.face).length := by
    rw [List.length_map]
    exact j.2
  have hget : (Delta.relatorCells.map RelatorCell.face)[i.1]'hi =
      (Delta.relatorCells.map RelatorCell.face)[j.1]'hj := by
    simpa [cell, List.getElem_map] using h
  exact Fin.ext ((List.Nodup.getElem_inj_iff hnodup).mp hget)

/-- A dart of a relator cell's boundary is based at that cell's face. -/
theorem faceOf_of_mem_cellDarts {i : Fin Delta.rCellCount} {d : Delta.toCombMap.Dart}
    (hd : d ∈ cellDarts Delta i) : Delta.toCombMap.faceOf d = (cell Delta i).face :=
  ((Delta.faceBoundary (cell Delta i).face).mem_iff d).mp hd

namespace RegionCandidate

/-- The cell at one end of a region: `true` is the source, `false` the target (for an interior
region). -/
def sideCell (a : RegionCandidate D eps Delta) (side : Bool) : Fin Delta.rCellCount :=
  if side then a.2.source else a.2.target.getD a.2.source

/-- **The crossing darts of a region.**  `side = true` reads the source arc and `side = false` the
target arc; `cellSide = true` takes the first dart of the arc, based at the cell, and
`cellSide = false` its reverse, based inside the region. -/
noncomputable def cross (a : RegionCandidate D eps Delta) (side cellSide : Bool) :
    Option Delta.toCombMap.Dart :=
  if cellSide then
    (if side then a.2.sourceArc.darts.head? else a.2.targetArc.darts.head?)
  else
    (if side then a.2.sourceArc.darts.head? else a.2.targetArc.darts.head?).map
      Delta.toCombMap.alpha

theorem cross_false (a : RegionCandidate D eps Delta) (side : Bool) :
    cross a side false = (cross a side true).map Delta.toCombMap.alpha := by
  simp [cross]

theorem cross_alpha (a : RegionCandidate D eps Delta) (side cellSide : Bool)
    (d : Delta.toCombMap.Dart) :
    cross a side (!cellSide) = some (Delta.toCombMap.alpha d) ↔ cross a side cellSide = some d := by
  cases cellSide with
  | true =>
      simp only [Bool.not_true, cross_false, Option.map_eq_some_iff]
      constructor
      · rintro ⟨p, hp, hpd⟩
        rw [Delta.toCombMap.alpha.injective hpd] at hp
        exact hp
      · intro h
        exact ⟨d, h, rfl⟩
  | false =>
      simp only [Bool.not_false, cross_false, Option.map_eq_some_iff]
      constructor
      · intro h
        exact ⟨Delta.toCombMap.alpha d, h, Delta.toCombMap.alpha_involutive d⟩
      · rintro ⟨p, hp, hpd⟩
        rw [← hpd, Delta.toCombMap.alpha_involutive]
        exact hp

theorem exists_cross (a : RegionCandidate D eps Delta)
    (hnondeg : 0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length) (side cellSide : Bool) :
    ∃ d, cross a side cellSide = some d := by
  have hsrc : a.2.sourceArc.darts ≠ [] := by
    intro h
    have := a.2.sourceArc.darts_length
    rw [h] at this
    simp at this
    omega
  have htgt : a.2.targetArc.darts ≠ [] := by
    intro h
    have := a.2.targetArc.darts_length
    rw [h] at this
    simp at this
    omega
  have hsome : ∃ p, (if side then a.2.sourceArc.darts.head? else a.2.targetArc.darts.head?) =
      some p := by
    cases side with
    | true => exact ⟨_, List.head?_eq_some_head hsrc⟩
    | false => exact ⟨_, List.head?_eq_some_head htgt⟩
  obtain ⟨p, hp⟩ := hsome
  cases cellSide with
  | true => exact ⟨p, by simp only [cross, if_true]; exact hp⟩
  | false => exact ⟨Delta.toCombMap.alpha p, by rw [cross_false]; simp [cross, hp]⟩

/-- A cell-side crossing dart lies on the arc, hence on the boundary of its cell. -/
theorem faceOf_cross_true (a : RegionCandidate D eps Delta) (hinterior : a.2.target.isSome)
    {side : Bool} {d : Delta.toCombMap.Dart} (h : cross a side true = some d) :
    Delta.toCombMap.faceOf d = (cell Delta (sideCell a side)).face := by
  cases side with
  | true =>
      simp only [cross, if_true] at h
      have hmem := a.2.sourceArc.mem_cycle_of_mem_darts (List.mem_of_mem_head? h)
      exact faceOf_of_mem_cellDarts hmem
  | false =>
      simp only [cross, if_true] at h
      obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hinterior
      have hmem := a.2.targetArc.mem_cycle_of_mem_darts (List.mem_of_mem_head? h)
      rw [hj] at hmem
      have hside : sideCell a false = j := by simp [sideCell, hj]
      rw [hside]
      exact faceOf_of_mem_cellDarts hmem

/-- A region-side crossing dart lies on the region's boundary cycle. -/
theorem mem_cycle_cross_false (a : RegionCandidate D eps Delta) (hinterior : a.2.target.isSome)
    {side : Bool} {d : Delta.toCombMap.Dart} (h : cross a side false = some d) :
    d ∈ a.2.boundary.cycle := by
  rw [cross_false, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  rw [a.2.boundary_decomposition]
  cases side with
  | true =>
      simp only [cross, if_true] at hp
      have hmem : Delta.toCombMap.alpha p ∈ a.2.sourceArc.reverseDarts := by
        simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
        exact ⟨p, List.mem_of_mem_head? hp, rfl⟩
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hmem))
  | false =>
      simp only [cross, if_true] at hp
      have hmem : Delta.toCombMap.alpha p ∈ a.2.targetArc.reverseDarts := by
        simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
        exact ⟨p, List.mem_of_mem_head? hp, rfl⟩
      have hne : a.2.target ≠ none := by
        intro hnone
        rw [hnone] at hinterior
        exact absurd hinterior (by simp)
      simp only [List.mem_append]
      exact Or.inl (Or.inr (mem_targetBoundaryDarts_of_ne_none Delta a.2.target a.2.targetArc
        hne _ hmem))

theorem faceOf_cross_false (a : RegionCandidate D eps Delta) (hinterior : a.2.target.isSome)
    {side : Bool} {d : Delta.toCombMap.Dart} (h : cross a side false = some d) :
    Delta.toCombMap.faceOf d ∈ a.1 :=
  ((a.2.boundary.cycle_mem_iff d).mp (mem_cycle_cross_false a hinterior h)).1

/-- **The data of `Φ_M`**: the ambient family and the selected edges. -/
structure PhiData (family E : Finset (RegionCandidate D eps Delta)) : Prop where
  subset : E ⊆ family
  pairwise : EstimatingSelection.PairwiseCompatible Compatible family
  cell_not_mem : ∀ a ∈ family, ∀ i : Fin Delta.rCellCount, (cell Delta i).face ∉ a.1
  interior : ∀ a ∈ E, a.2.target.isSome
  nondegenerate : ∀ a ∈ E, 0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length
  noLoop : ∀ a ∈ E, a.2.target ≠ some a.2.source
  noMultiple : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → ∀ i j : Fin Delta.rCellCount,
    ((a.2.source = i ∧ a.2.target = some j) ∨ (a.2.source = j ∧ a.2.target = some i)) →
    ((b.2.source = i ∧ b.2.target = some j) ∨ (b.2.source = j ∧ b.2.target = some i)) → False

variable {family E : Finset (RegionCandidate D eps Delta)}

theorem PhiData.sideCell_ne (P : PhiData family E) {a : RegionCandidate D eps Delta}
    (ha : a ∈ E) : sideCell a true ≠ sideCell a false := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (P.interior a ha)
  have hloop := P.noLoop a ha
  have hfalse : sideCell a false = j := by
    show a.2.target.getD a.2.source = j
    simp only [hj, Option.getD_some]
  show a.2.source ≠ sideCell a false
  rw [hfalse]
  intro h
  exact hloop (by rw [hj, h])

theorem PhiData.face_not_mem_of_cross_true (P : PhiData family E) {a : RegionCandidate D eps Delta}
    (ha : a ∈ E) {side : Bool} {d : Delta.toCombMap.Dart} (h : cross a side true = some d) :
    ∀ b ∈ family, Delta.toCombMap.faceOf d ∉ b.1 := by
  intro b hb
  rw [faceOf_cross_true a (P.interior a ha) h]
  exact P.cell_not_mem b hb _

/-- **A crossing dart determines its region, side and orientation.** -/
theorem PhiData.cross_unique (P : PhiData family E) {a b : RegionCandidate D eps Delta}
    (ha : a ∈ E) (hb : b ∈ E) {s s' o o' : Bool} {d : Delta.toCombMap.Dart}
    (h : cross a s o = some d) (h' : cross b s' o' = some d) : a = b ∧ s = s' ∧ o = o' := by
  have hfam : ∀ x ∈ E, x ∈ family := fun x hx => P.subset hx
  -- the orientation
  have horient : o = o' := by
    cases o with
    | true =>
        cases o' with
        | true => rfl
        | false =>
            exfalso
            exact P.face_not_mem_of_cross_true ha h b (hfam b hb)
              (faceOf_cross_false b (P.interior b hb) h')
    | false =>
        cases o' with
        | true =>
            exfalso
            exact P.face_not_mem_of_cross_true hb h' a (hfam a ha)
              (faceOf_cross_false a (P.interior a ha) h)
        | false => rfl
  subst horient
  -- the region
  have hregion : a = b := by
    cases o with
    | false =>
        exact eq_of_face_mem_of_face_mem P.pairwise (hfam a ha) (hfam b hb)
          (faceOf_cross_false a (P.interior a ha) h) (faceOf_cross_false b (P.interior b hb) h')
    | true =>
        have hα : cross a s false = some (Delta.toCombMap.alpha d) :=
          (cross_alpha a s true d).mpr h
        have hα' : cross b s' false = some (Delta.toCombMap.alpha d) :=
          (cross_alpha b s' true d).mpr h'
        exact eq_of_face_mem_of_face_mem P.pairwise (hfam a ha) (hfam b hb)
          (faceOf_cross_false a (P.interior a ha) hα) (faceOf_cross_false b (P.interior b hb) hα')
  subst hregion
  refine ⟨rfl, ?_, rfl⟩
  -- the side
  have hcell : ∀ o : Bool, ∀ s s' : Bool, ∀ x, cross a s o = some x → cross a s' o = some x →
      s = s' := by
    intro o s s' x hx hx'
    cases o with
    | true =>
        have hf := faceOf_cross_true a (P.interior a ha) hx
        have hf' := faceOf_cross_true a (P.interior a ha) hx'
        have hidx := cell_face_injective Delta (hf.symm.trans hf')
        by_contra hne
        have hsc := P.sideCell_ne ha
        cases s <;> cases s' <;> simp_all
    | false =>
        have hy := (cross_alpha a s true (Delta.toCombMap.alpha x)).mp
          (by rw [Bool.not_true, Delta.toCombMap.alpha_involutive]; exact hx)
        have hy' := (cross_alpha a s' true (Delta.toCombMap.alpha x)).mp
          (by rw [Bool.not_true, Delta.toCombMap.alpha_involutive]; exact hx')
        have hf := faceOf_cross_true a (P.interior a ha) hy
        have hf' := faceOf_cross_true a (P.interior a ha) hy'
        have hidx := cell_face_injective Delta (hf.symm.trans hf')
        by_contra hne
        have hsc := P.sideCell_ne ha
        cases s <;> cases s' <;> simp_all
  exact hcell o s s' d h h'

/-- The retained darts of `Φ_M` in the dual of the collapsed map. -/
def PhiKeep (family E : Finset (RegionCandidate D eps Delta))
    (x : (collapsedMap family).Dart) : Prop :=
  ∃ a ∈ E, ∃ s o : Bool, cross a s o = some x.1

theorem phiKeep_alpha (x : (collapsedMap family).dual.Dart) :
    PhiKeep family E ((collapsedMap family).dual.alpha x) ↔ PhiKeep family E x := by
  constructor
  · rintro ⟨a, ha, s, o, h⟩
    refine ⟨a, ha, s, !o, ?_⟩
    have h' : cross a s o = some (Delta.toCombMap.alpha x.1) := h
    have := (cross_alpha a s (!o) x.1).mp
    rw [Bool.not_not] at this
    exact this h'
  · rintro ⟨a, ha, s, o, h⟩
    exact ⟨a, ha, s, !o, (cross_alpha a s o x.1).mpr h⟩

/-- **Osin's `Φ_M`, subdivided**: the restriction of the dual of the collapsed map to the crossing
darts. -/
noncomputable def phiMap (family E : Finset (RegionCandidate D eps Delta)) : CombMap.{v} :=
  CombMap.PredicateRestriction.toCombMap (collapsedMap family).dual (PhiKeep family E)
    phiKeep_alpha

theorem phiMap_isRestriction (family E : Finset (RegionCandidate D eps Delta)) :
    (collapsedMap family).dual.IsRestriction (phiMap family E)
      (Function.Embedding.subtype (PhiKeep family E)) :=
  CombMap.PredicateRestriction.isRestriction _ _ _

/-- The region of a retained dart. -/
noncomputable def phiRegion (y : (phiMap family E).Dart) : RegionCandidate D eps Delta :=
  Classical.choose y.2

theorem phiRegion_mem (y : (phiMap family E).Dart) : phiRegion y ∈ E :=
  (Classical.choose_spec y.2).1

/-- The side of a retained dart. -/
noncomputable def phiSide (y : (phiMap family E).Dart) : Bool :=
  Classical.choose (Classical.choose_spec y.2).2

/-- The orientation of a retained dart: `true` at a cell, `false` at a midpoint. -/
noncomputable def phiCellSide (y : (phiMap family E).Dart) : Bool :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec y.2).2)

theorem phi_cross (y : (phiMap family E).Dart) :
    cross (phiRegion y) (phiSide y) (phiCellSide y) = some y.1.1 :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec y.2).2)

theorem PhiData.phi_eq (P : PhiData family E) (y : (phiMap family E).Dart)
    {a : RegionCandidate D eps Delta} (ha : a ∈ E) {s o : Bool} (h : cross a s o = some y.1.1) :
    phiRegion y = a ∧ phiSide y = s ∧ phiCellSide y = o :=
  P.cross_unique (phiRegion_mem y) ha (phi_cross y) h

/-- The retained dart at a crossing. -/
noncomputable def phiDart (P : PhiData family E) (a : RegionCandidate D eps Delta) (ha : a ∈ E)
    (s o : Bool) : (phiMap family E).Dart :=
  let d := Classical.choose (exists_cross a (P.nondegenerate a ha) s o)
  have hd : cross a s o = some d := Classical.choose_spec (exists_cross a (P.nondegenerate a ha) s o)
  have hkeep : ¬ RegionInternal family d := by
    cases o with
    | true =>
        exact not_regionInternal_of_face_not_mem (P.face_not_mem_of_cross_true ha hd)
    | false =>
        exact not_regionInternal_of_mem_cycle P.pairwise (P.subset ha)
          (mem_cycle_cross_false a (P.interior a ha) hd)
  ⟨⟨d, hkeep⟩, a, ha, s, o, hd⟩

theorem phiDart_cross (P : PhiData family E) (a : RegionCandidate D eps Delta) (ha : a ∈ E)
    (s o : Bool) : cross a s o = some (phiDart P a ha s o).1.1 :=
  Classical.choose_spec (exists_cross a (P.nondegenerate a ha) s o)

theorem dart_ext {y z : (phiMap family E).Dart}
    (hregion : phiRegion y = phiRegion z) (hside : phiSide y = phiSide z)
    (hcell : phiCellSide y = phiCellSide z) : y = z := by
  have h1 := phi_cross y
  rw [hregion, hside, hcell] at h1
  exact Subtype.ext (Subtype.ext (Option.some.inj (h1.symm.trans (phi_cross z))))

theorem PhiData.joins_of_sides (P : PhiData family E) {a : RegionCandidate D eps Delta}
    (ha : a ∈ E) {s t : Bool} (hst : s ≠ t) :
    (a.2.source = sideCell a s ∧ a.2.target = some (sideCell a t)) ∨
      (a.2.source = sideCell a t ∧ a.2.target = some (sideCell a s)) := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (P.interior a ha)
  cases s <;> cases t
  · exact absurd rfl hst
  · right
    simp [sideCell, hj]
  · left
    simp [sideCell, hj]
  · exact absurd rfl hst

/-- Retained darts share a vertex of `Φ_M` exactly when they lie in one face of the collapsed map. -/
theorem phiMap_vertexOf_eq_iff (y z : (phiMap family E).Dart) :
    (phiMap family E).vertexOf y = (phiMap family E).vertexOf z ↔
      (collapsedMap family).faceOf y.1 = (collapsedMap family).faceOf z.1 := by
  rw [(phiMap_isRestriction family E).vertexOf_eq_iff, CombMap.vertexOf_eq_iff,
    CombMap.faceOf_eq_iff]
  rfl

/-- **Faces of the collapsed map outside the regions, from faces of the diagram.** -/
theorem collapsed_faceOf_eq_of_face_eq {d d' : Delta.toCombMap.Dart}
    (hface : ∀ a ∈ family, Delta.toCombMap.faceOf d ∉ a.1)
    (heq : Delta.toCombMap.faceOf d = Delta.toCombMap.faceOf d') :
    (collapsedMap family).faceOf ⟨d, not_regionInternal_of_face_not_mem hface⟩ =
      (collapsedMap family).faceOf ⟨d', not_regionInternal_of_face_not_mem (heq ▸ hface)⟩ := by
  have hcycle : Delta.toCombMap.facePerm.SameCycle d d' :=
    (Delta.toCombMap.faceOf_eq_iff d d').mp heq
  obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
  have hpow : ∀ m : ℕ, ∃ hm : ∀ a ∈ family,
      Delta.toCombMap.faceOf ((Delta.toCombMap.facePerm ^ m) d) ∉ a.1,
      (collapsedMap family).faceOf ⟨d, not_regionInternal_of_face_not_mem hface⟩ =
        (collapsedMap family).faceOf ⟨(Delta.toCombMap.facePerm ^ m) d,
          not_regionInternal_of_face_not_mem hm⟩ := by
    intro m
    induction m with
    | zero => exact ⟨hface, rfl⟩
    | succ m ih =>
        obtain ⟨hm, hfm⟩ := ih
        have hm' : ∀ a ∈ family,
            Delta.toCombMap.faceOf ((Delta.toCombMap.facePerm ^ (m + 1)) d) ∉ a.1 := by
          rw [pow_succ', Perm.mul_apply, Delta.toCombMap.faceOf_facePerm]
          exact hm
        refine ⟨hm', ?_⟩
        have hstep := CombMap.faceOf_facePerm (collapsedMap family)
          ⟨(Delta.toCombMap.facePerm ^ m) d, not_regionInternal_of_face_not_mem hm⟩
        rw [collapsed_facePerm_of_face_not_mem hm] at hstep
        have hsucc : (Delta.toCombMap.facePerm ^ (m + 1)) d =
            Delta.toCombMap.facePerm ((Delta.toCombMap.facePerm ^ m) d) := by
          rw [pow_succ', Perm.mul_apply]
        rw [hfm, ← hstep]
        exact congrArg (collapsedMap family).faceOf (Subtype.ext hsucc.symm)
  obtain ⟨_, hfn⟩ := hpow n
  exact hfn.trans (congrArg (collapsedMap family).faceOf (Subtype.ext hn))

variable (P : PhiData family E)

/-- **`Φ_M` subdivided is a `SubdividedGraph`.** -/
noncomputable def phiSubdividedGraph :
    CombMap.SubdividedGraph (phiMap family E) (RegionCandidate D eps Delta)
      (Fin Delta.rCellCount) where
  IsCellDart y := phiCellSide y = true
  region := phiRegion
  endCell y := sideCell (phiRegion y) (phiSide y)
  cellDart_alpha y := by
    have h := (cross_alpha (phiRegion y) (phiSide y) (phiCellSide y) y.1.1).mpr (phi_cross y)
    obtain ⟨-, -, hcell⟩ := P.phi_eq ((phiMap family E).alpha y) (phiRegion_mem y) h
    rw [hcell]
    cases phiCellSide y <;> simp
  region_alpha y := by
    have h := (cross_alpha (phiRegion y) (phiSide y) (phiCellSide y) y.1.1).mpr (phi_cross y)
    exact (P.phi_eq ((phiMap family E).alpha y) (phiRegion_mem y) h).1
  endCell_alpha y := by
    have h := (cross_alpha (phiRegion y) (phiSide y) (phiCellSide y) y.1.1).mpr (phi_cross y)
    obtain ⟨hr, hs, -⟩ := P.phi_eq ((phiMap family E).alpha y) (phiRegion_mem y) h
    simp only [hr, hs]
  cellDart_of_vertex y z hyz := by
    rw [phiMap_vertexOf_eq_iff] at hyz
    -- a cell dart and a midpoint dart never share a face of the collapsed map
    have hcase : ∀ (p q : (phiMap family E).Dart), phiCellSide p = true →
        phiCellSide q = false →
        (collapsedMap family).faceOf p.1 = (collapsedMap family).faceOf q.1 → False := by
      intro p q hp hq hpq
      have hpc := phi_cross p
      rw [hp] at hpc
      have hqc := phi_cross q
      rw [hq] at hqc
      have hface := P.face_not_mem_of_cross_true (phiRegion_mem p) hpc
      have hq_face := collapsed_faceOf_eq_imp_face_eq hface q.1 hpq.symm
      have hmem := faceOf_cross_false (phiRegion q) (P.interior _ (phiRegion_mem q)) hqc
      rw [hq_face] at hmem
      exact hface (phiRegion q) (P.subset (phiRegion_mem q)) hmem
    cases hy : phiCellSide y <;> cases hz : phiCellSide z
    · simp
    · exact (hcase z y hz hy hyz.symm).elim
    · exact (hcase y z hy hz hyz).elim
    · simp
  endCell_of_vertex y z hy hz hyz := by
    rw [phiMap_vertexOf_eq_iff] at hyz
    have hyc := phi_cross y
    rw [show phiCellSide y = true from hy] at hyc
    have hzc := phi_cross z
    rw [show phiCellSide z = true from hz] at hzc
    have hface := P.face_not_mem_of_cross_true (phiRegion_mem y) hyc
    have hzf := collapsed_faceOf_eq_imp_face_eq hface z.1 hyz.symm
    have hf := faceOf_cross_true (phiRegion y) (P.interior _ (phiRegion_mem y)) hyc
    have hf' := faceOf_cross_true (phiRegion z) (P.interior _ (phiRegion_mem z)) hzc
    exact cell_face_injective Delta (hf.symm.trans (hzf.symm.trans hf'))
  region_of_vertex y z hy hz hyz := by
    rw [phiMap_vertexOf_eq_iff] at hyz
    have hyc := phi_cross y
    rw [show phiCellSide y = false by simpa using hy] at hyc
    have hzc := phi_cross z
    rw [show phiCellSide z = false by simpa using hz] at hzc
    have hymem := mem_cycle_cross_false (phiRegion y) (P.interior _ (phiRegion_mem y)) hyc
    have hzmem := mem_cycle_of_collapsed_faceOf_eq P.pairwise (P.subset (phiRegion_mem y))
      hymem z.1 hyz.symm
    have hzface : Delta.toCombMap.faceOf z.1.1 ∈ (phiRegion y).1 :=
      (((phiRegion y).2.boundary.cycle_mem_iff _).mp hzmem).1
    exact eq_of_face_mem_of_face_mem P.pairwise (P.subset (phiRegion_mem y))
      (P.subset (phiRegion_mem z)) hzface
      (faceOf_cross_false (phiRegion z) (P.interior _ (phiRegion_mem z)) hzc)
  sigma_ne_of_midpoint y hy := by
    have hyc := phi_cross y
    rw [show phiCellSide y = false by simpa using hy] at hyc
    have hzc := phiDart_cross P (phiRegion y) (phiRegion_mem y) (!phiSide y) false
    have hzside : phiSide (phiDart P (phiRegion y) (phiRegion_mem y) (!phiSide y) false) =
        !phiSide y :=
      (P.phi_eq _ (phiRegion_mem y) hzc).2.1
    have hzy : phiDart P (phiRegion y) (phiRegion_mem y) (!phiSide y) false ≠ y := by
      intro h
      rw [h] at hzside
      cases hs : phiSide y <;> simp [hs] at hzside
    have hymem := mem_cycle_cross_false (phiRegion y) (P.interior _ (phiRegion_mem y)) hyc
    have hzmem := mem_cycle_cross_false (phiRegion y) (P.interior _ (phiRegion_mem y)) hzc
    have hface := collapsed_faceOf_eq_of_mem_cycle P.pairwise (P.subset (phiRegion_mem y))
      hymem hzmem
    have hcycle : (collapsedMap family).dual.sigma.SameCycle
        ((Function.Embedding.subtype (PhiKeep family E)) y)
        ((Function.Embedding.subtype (PhiKeep family E))
          (phiDart P (phiRegion y) (phiRegion_mem y) (!phiSide y) false)) :=
      ((collapsedMap family).faceOf_eq_iff _ _).mp hface
    exact PermFirstReturn.apply_ne_self_of_sameCycle
      (CombMap.PredicateRestriction.sigma_firstReturn (collapsedMap family).dual (PhiKeep family E))
      hzy hcycle
  endCell_ne y z hy hz hregion hne := by
    have hyo : phiCellSide y = false := by simpa using hy
    have hzo : phiCellSide z = false := by simpa using hz
    have hside : phiSide y ≠ phiSide z :=
      fun hs => hne (dart_ext hregion.symm hs (hyo.trans hzo.symm))
    have hsc := P.sideCell_ne (phiRegion_mem y)
    change sideCell (phiRegion y) (phiSide y) ≠ sideCell (phiRegion z) (phiSide z)
    rw [hregion]
    intro heq
    cases hsy : phiSide y <;> cases hsz : phiSide z
    · exact hside (hsy.trans hsz.symm)
    · rw [hsy, hsz] at heq
      exact hsc heq.symm
    · rw [hsy, hsz] at heq
      exact hsc heq
    · exact hside (hsy.trans hsz.symm)
  midpoint_two d e x hd he hx hed hxd hde := by
    have hdo : phiCellSide d = false := by simpa using hd
    have heo : phiCellSide e = false := by simpa using he
    have hxo : phiCellSide x = false := by simpa using hx
    have hside : phiSide d ≠ phiSide e :=
      fun hs => hde (dart_ext hed.symm hs (hdo.trans heo.symm))
    by_cases hxs : phiSide x = phiSide d
    · exact Or.inl (dart_ext hxd hxs (hxo.trans hdo.symm))
    · refine Or.inr (dart_ext (hxd.trans hed.symm) ?_ (hxo.trans heo.symm))
      revert hxs hside
      cases phiSide x <;> cases phiSide d <;> cases phiSide e <;> decide
  noMultiple d e d' e' hd he hd' he' hed he'd' hde hd'e' hend hend' := by
    by_contra hab
    have hdo : phiCellSide d = false := by simpa using hd
    have heo : phiCellSide e = false := by simpa using he
    have hd'o : phiCellSide d' = false := by simpa using hd'
    have he'o : phiCellSide e' = false := by simpa using he'
    have hsde : phiSide d ≠ phiSide e :=
      fun hs => hde (dart_ext hed.symm hs (hdo.trans heo.symm))
    have hsde' : phiSide d' ≠ phiSide e' :=
      fun hs => hd'e' (dart_ext he'd'.symm hs (hd'o.trans he'o.symm))
    have h1 := P.joins_of_sides (phiRegion_mem d) hsde
    have h2 := P.joins_of_sides (phiRegion_mem d') hsde'
    have hend1 : sideCell (phiRegion d) (phiSide d) = sideCell (phiRegion d') (phiSide d') := hend
    have hend2 : sideCell (phiRegion d) (phiSide e) = sideCell (phiRegion d') (phiSide e') := by
      have h := (hend' : sideCell (phiRegion e) (phiSide e) = sideCell (phiRegion e') (phiSide e'))
      rw [hed, he'd'] at h
      exact h
    rw [← hend1, ← hend2] at h2
    exact P.noMultiple (phiRegion d) (phiRegion_mem d) (phiRegion d') (phiRegion_mem d') hab
      _ _ h1 h2

end RegionCandidate
end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.cell_face_injective
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.exists_cross
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.PhiData.cross_unique
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.collapsed_faceOf_eq_of_face_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.phiSubdividedGraph
