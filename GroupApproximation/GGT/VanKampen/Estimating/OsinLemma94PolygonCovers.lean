import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PlanarPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSharedEdge
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhi
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the unbound darts off the selected regions lie on (A1) sides

Osin (math/0411039v3, §9), Lemma 9.4: "Let `S` denote the sum of lengths of all unbound arcs
of type (A1) in `Δ`.  Then `S < n √ρ`."  `OsinLemma94PlanarPieces.lean` reduces the diagram
half to `OsinLemma94PolygonCountInput`, whose second half is `P.Covers L`: the unbound darts are
covered by the (A1) sides of the polygons, except for at most `L n` of them.

Take an unbound dart `d` of cell `i` in an optimal family whose relator words do not have value
one, and look at the face across `d`.

* It is not cell `i` itself, by hypothesis: a region from a cell to itself is not a candidate
  (`RespectsSections`), so doubling the edge would give no contradiction there.
* It is no other relator cell and not the exterior (`alpha_faceOf_not_cell_of_unbound`).
  Otherwise doubling the edge of `d` adjoins a region and contradicts maximality
  (`RealizedSectionFamily.false_of_unbound_shared_edge`).
* If it lies in no selected region, it is the face of a polygon, and the reverse of `d` lies on
  a side of kind `cell` (`exists_relatorSide_of_unbound`).  A boundary side runs along `∂Δ`, so
  `d` would be exterior.  A cutting side has the polygon face on both sides, which is no cell.
  A short side has a selected region across, which contains no cell.
* The remaining unbound darts face a selected region.

So `S` is at most the number of darts on (A1) sides plus the number of unbound darts facing a
selected region (`covers_of_regionFacing_le`).  The relator words of `W` have length at least
`ρ > c / λ` and are `(λ, c)`-quasi-geodesic, so none has value one
(`OsinCCondition.listVal_ne_one_of_mem`).
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

namespace OsinLemma94PolygonCovers

/-- A word read from `v` ends at `v` times its value. -/
theorem vertex_length_eq {G : Type u} [Group G] {Lambda : Type w} (v : G)
    (word : List (RelLetter G Lambda)) :
    OsinComponents.vertex v word word.length = v * RelLetter.listVal word := by
  induction word generalizing v with
  | nil => simp [RelLetter.listVal_nil]
  | cons a t ih =>
    rw [List.length_cons, OsinComponents.vertex_cons_succ, ih]
    simp only [RelLetter.listVal, List.map_cons, List.prod_cons, mul_assoc]

end OsinLemma94PolygonCovers

/-- **A relator word of length at least `ρ > c / λ` does not have value one.**  The word is
`(λ, c)`-quasi-geodesic, so its endpoints are at distance at least `λ ρ - c > 0`. -/
theorem OsinCCondition.listVal_ne_one_of_mem {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps : ℕ}
    {mu lambda c : ℝ} {rho : ℕ} (hW : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hrho : c < lambda * rho) {word : List (RelLetter G Lambda)}
    (hword : word ∈ W) : RelLetter.listVal word ≠ 1 := by
  intro hone
  have hq := (hW.quasiGeodesic word hword).2 0 word.length (Nat.zero_le _) le_rfl
  rw [OsinComponents.vertex_zero, OsinLemma94PolygonCovers.vertex_length_eq, hone, one_mul,
    WordMetric.wordDist_self, Nat.sub_zero, Nat.cast_zero] at hq
  have hlong : (rho : ℝ) ≤ word.length := by exact_mod_cast hW.long word hword
  have hmul : lambda * (rho : ℝ) ≤ lambda * word.length :=
    mul_le_mul_of_nonneg_left hlong hlambda.le
  linarith

namespace GloballyDistinguishedSectionFamily

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- The relator cells of the optimal diagram do not have value one. -/
theorem cell_listVal_ne_one (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {epsC : ℕ} {mu : ℝ} {rho : ℕ} (hW : OsinCCondition D W epsC mu lambda c rho)
    (hlambda : 0 < lambda) (hrho : c < lambda * rho) :
    ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1 :=
  fun C _ => OsinCCondition.listVal_ne_one_of_mem hW hlambda hrho C.word_mem

/-- The relator cells of the optimal diagram have at least two darts. -/
theorem one_lt_cellDarts_length
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {epsC : ℕ} {mu lambdaC cC : ℝ} {rho : ℕ} (hW : OsinCCondition D W epsC mu lambdaC cC rho)
    (hrho : 1 < rho) (i : Fin S.diagram.rCellCount) :
    1 < (cellDarts S.diagram i).length := by
  rw [CellBoundaryPartition.cellDarts_length_eq_word_length]
  exact lt_of_lt_of_le hrho (hW.long _ (cell S.diagram i).word_mem)

/-- **The face across an unbound dart is no relator cell and not the exterior**, if it is not
the cell of the dart.  Otherwise the edge is doubled into a digon region from the cell to a
different cell or to the exterior, which contradicts maximality. -/
theorem alpha_faceOf_not_cell_of_unbound
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hlen : ∀ i : Fin S.diagram.rCellCount, 1 < (cellDarts S.diagram i).length)
    {i : Fin S.diagram.rCellCount} {d : S.diagram.toCombMap.Dart}
    (hd : d ∈ RegionCandidate.unboundDarts S.family i)
    (hsame : (cell S.diagram i).face ≠
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)) :
    (∀ j : Fin S.diagram.rCellCount,
        (cell S.diagram j).face ≠ S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)) ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ≠ S.diagram.outerFace := by
  refine ⟨fun j hj => ?_, fun hout => S.toRealizedSectionFamily.false_of_unbound_shared_edge
    S.label_admissible S.weight_maximal hvalue i d hd (hlen i) (Or.inr hout)⟩
  by_cases hji : j = i
  · subst hji
    exact hsame hj
  · exact S.toRealizedSectionFamily.false_of_unbound_shared_edge S.label_admissible
      S.weight_maximal hvalue i d hd (hlen i) (Or.inl ⟨j, hji, hj.symm⟩)

/-- The unbound darts of cell `i` whose reverse lies in no selected region. -/
noncomputable def unboundOffRegions
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (i : Fin S.diagram.rCellCount) : Finset S.diagram.toCombMap.Dart :=
  (RegionCandidate.unboundDarts S.family i).filter fun d =>
    ¬ ∃ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1

end GloballyDistinguishedSectionFamily

namespace OsinLemma94RealizedPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- The darts of the (A1) sides of all polygons. -/
noncomputable def relatorSideDarts (P : OsinLemma94RealizedPolygons S) :
    Finset S.diagram.toCombMap.Dart :=
  Finset.univ.biUnion fun k => (Finset.range (P.sideCount k)).biUnion fun s =>
    if s ∈ P.relatorSides k then (P.sideDarts k s).toFinset else ∅

/-- The (A1) sides carry at most `∑ S_i` darts. -/
theorem card_relatorSideDarts_le (P : OsinLemma94RealizedPolygons S) :
    (P.relatorSideDarts.card : ℝ) ≤
      ∑ k, classWordLength (P.word k) (P.sideCount k) (P.relatorSides k) := by
  have h : P.relatorSideDarts.card ≤ ∑ k, ∑ s ∈ Finset.range (P.sideCount k),
      (if s ∈ P.relatorSides k then (P.sideDarts k s).toFinset else ∅).card := by
    unfold relatorSideDarts
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun k _ => ?_)
    exact Finset.card_biUnion_le
  refine le_trans (Nat.cast_le.mpr h) ?_
  rw [Nat.cast_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Nat.cast_sum, classWordLength]
  refine Finset.sum_le_sum fun s _ => ?_
  split_ifs
  · simp only [OsinLemma94RealizedPolygons.word, dartWord, List.length_map]
    exact_mod_cast List.toFinset_card_le (l := P.sideDarts k s)
  · simp

/-- **An unbound dart facing no cell, no exterior and no selected region lies across an (A1)
side.**  The face across it is the face of a polygon.  The side of that polygon through the
reverse dart is not a boundary side, since the dart would be exterior; not a cutting side,
since the polygon face is no cell; and not a short side, since a selected region contains no
cell. -/
theorem exists_relatorSide_of_unbound (P : OsinLemma94RealizedPolygons S)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    {i : Fin S.diagram.rCellCount} {d : S.diagram.toCombMap.Dart}
    (hd : d ∈ cellDarts S.diagram i)
    (hcell : ∀ j : Fin S.diagram.rCellCount,
      (cell S.diagram j).face ≠ S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d))
    (hout : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ≠ S.diagram.outerFace)
    (hreg : ¬ ∃ a ∈ S.family,
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1) :
    ∃ k s, s < P.sideCount k ∧ s ∈ P.relatorSides k ∧
      S.diagram.toCombMap.alpha d ∈ P.sideDarts k s := by
  have hface : S.diagram.toCombMap.faceOf d = (cell S.diagram i).face :=
    faceOf_of_mem_cellDarts hd
  have halpha : S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha d) = d :=
    S.diagram.toCombMap.alpha_involutive d
  obtain ⟨k, hk⟩ := P.face_complete _ hout hcell fun a ha hmem => hreg ⟨a, ha, hmem⟩
  have hwalk : S.diagram.toCombMap.alpha d ∈
      (List.range (P.sideCount k)).flatMap (P.sideDarts k) := by
    rw [← P.walk k, List.mem_rotate]
    exact ((S.diagram.faceBoundary (P.face k)).mem_iff _).mpr hk.symm
  obtain ⟨s, hs, hds⟩ := List.mem_flatMap.mp hwalk
  have hs' : s < P.sideCount k := List.mem_range.mp hs
  refine ⟨k, s, hs', ?_, hds⟩
  show ∃ j, P.kind k s = OsinLemma94SideClass.cell j
  cases hkind : P.kind k s with
  | cell j => exact ⟨j, rfl⟩
  | boundary j =>
    exfalso
    obtain ⟨_, arc, harc, -⟩ := P.boundary_arc k s j hs' hkind
    rw [harc] at hds
    have hmem : S.diagram.toCombMap.alpha d ∈
        (S.diagram.faceBoundary S.diagram.outerFace).darts.reverse.map
          S.diagram.toCombMap.alpha :=
      arc.mem_cycle_of_mem_darts hds
    obtain ⟨e, he, hea⟩ := List.mem_map.mp hmem
    rw [S.diagram.toCombMap.alpha_involutive.injective hea] at he
    exact (cell S.diagram i).face_ne_outer
      (hface.symm.trans (((S.diagram.faceBoundary S.diagram.outerFace).mem_iff d).mp
        (List.mem_reverse.mp he)))
  | cutting =>
    exfalso
    have h := P.cutting_internal k s hs' hkind _ hds
    rw [halpha, hface] at h
    exact P.face_not_cell k i h
  | short =>
    exfalso
    obtain ⟨a, ha, hall⟩ := P.short_region k s hs' hkind
    have h := hall _ hds
    rw [halpha, hface] at h
    exact S.toRealizedSectionFamily.faces_not_mem_of_value hvalue a ha _ (cell_mem S.diagram i) h

/-- **The unbound darts facing no selected region number at most `∑ S_i`.**  Reversal maps them
injectively into the darts of the (A1) sides, and distinct cells have disjoint darts. -/
theorem sum_card_unboundOffRegions_le (P : OsinLemma94RealizedPolygons S)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hlen : ∀ i : Fin S.diagram.rCellCount, 1 < (cellDarts S.diagram i).length)
    (hsame : ∀ (i : Fin S.diagram.rCellCount) (d : S.diagram.toCombMap.Dart),
      d ∈ RegionCandidate.unboundDarts S.family i →
        (cell S.diagram i).face ≠ S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)) :
    (∑ i : Fin S.diagram.rCellCount, ((S.unboundOffRegions i).card : ℝ)) ≤
      ∑ k, classWordLength (P.word k) (P.sideCount k) (P.relatorSides k) := by
  have hmem : ∀ (i : Fin S.diagram.rCellCount) (d : S.diagram.toCombMap.Dart),
      d ∈ S.unboundOffRegions i → d ∈ cellDarts S.diagram i := fun i d hd =>
    List.mem_toFinset.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hd).1).1
  have hdisj : ((Finset.univ : Finset (Fin S.diagram.rCellCount)) :
      Set (Fin S.diagram.rCellCount)).PairwiseDisjoint S.unboundOffRegions := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun d hdi hdj => hij (cell_face_injective S.diagram ?_)
    exact (faceOf_of_mem_cellDarts (hmem i d hdi)).symm.trans
      (faceOf_of_mem_cellDarts (hmem j d hdj))
  have hmaps : Set.MapsTo S.diagram.toCombMap.alpha
      (Finset.univ.biUnion S.unboundOffRegions : Set S.diagram.toCombMap.Dart)
      (P.relatorSideDarts : Set S.diagram.toCombMap.Dart) := by
    intro d hd
    obtain ⟨i, -, hdi⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hd)
    obtain ⟨hdu, hreg⟩ := Finset.mem_filter.mp hdi
    obtain ⟨hcell, hout⟩ := S.alpha_faceOf_not_cell_of_unbound hvalue hlen hdu (hsame i d hdu)
    obtain ⟨k, s, hs, hrel, hds⟩ :=
      P.exists_relatorSide_of_unbound hvalue (hmem i d hdi) hcell hout hreg
    refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨s, Finset.mem_range.mpr hs, ?_⟩⟩)
    rw [if_pos hrel]
    exact List.mem_toFinset.mpr hds
  have hcard := Finset.card_le_card_of_injOn S.diagram.toCombMap.alpha hmaps
    S.diagram.toCombMap.alpha_involutive.injective.injOn
  rw [Finset.card_biUnion hdisj] at hcard
  have hreal : (∑ i : Fin S.diagram.rCellCount, ((S.unboundOffRegions i).card : ℝ)) ≤
      P.relatorSideDarts.card := by
    exact_mod_cast hcard
  exact hreal.trans P.card_relatorSideDarts_le

/-- **`S ≤ ∑ S_i` up to the unbound darts facing a selected region.**  If those number at most
`L n`, and no unbound dart has its own cell across, the polygons cover the unbound darts with
slack `L`. -/
theorem covers_of_regionFacing_le (P : OsinLemma94RealizedPolygons S)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hlen : ∀ i : Fin S.diagram.rCellCount, 1 < (cellDarts S.diagram i).length)
    (hsame : ∀ (i : Fin S.diagram.rCellCount) (d : S.diagram.toCombMap.Dart),
      d ∈ RegionCandidate.unboundDarts S.family i →
        (cell S.diagram i).face ≠ S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d))
    (L : ℕ)
    (hregion : ∑ i : Fin S.diagram.rCellCount,
      ((RegionCandidate.unboundDarts S.family i).filter fun d =>
        ∃ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1).card ≤
          L * Delta.rCellCount) :
    P.Covers L := by
  have hsplit : ∀ i : Fin S.diagram.rCellCount,
      ((RegionCandidate.unboundDarts S.family i).card : ℝ) =
        (((RegionCandidate.unboundDarts S.family i).filter fun d =>
          ∃ a ∈ S.family,
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1).card : ℝ) +
          ((S.unboundOffRegions i).card : ℝ) := by
    intro i
    exact_mod_cast (Finset.card_filter_add_card_filter_not _).symm
  have h2 : (∑ i : Fin S.diagram.rCellCount,
      (((RegionCandidate.unboundDarts S.family i).filter fun d =>
        ∃ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1).card :
          ℝ)) ≤ (L : ℝ) * Delta.rCellCount := by
    exact_mod_cast hregion
  have h3 := P.sum_card_unboundOffRegions_le hvalue hlen hsame
  unfold Covers
  simp only [hsplit, Finset.sum_add_distrib]
  linarith

end OsinLemma94RealizedPolygons

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94PolygonCovers.vertex_length_eq
#audit_axioms GroupApproximation.GGT.VanKampen.OsinCCondition.listVal_ne_one_of_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.cell_listVal_ne_one
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.one_lt_cellDarts_length
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.alpha_faceOf_not_cell_of_unbound
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.card_relatorSideDarts_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.exists_relatorSide_of_unbound
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.sum_card_unboundOffRegions_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.covers_of_regionFacing_le

end GroupApproximation.GGT.VanKampen
