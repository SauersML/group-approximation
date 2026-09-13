import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonRealization
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonLists
import Mathlib.Data.List.SplitBy
import GroupApproximation.Meta.AxiomGuard

/-!
# The sides of the polygons of Lemma 9.4

What lies across a dart of the walk of an unselected `G`-face, and the cut of the walk into
sides, for `OsinLemma94PolygonPartitionInput`.

* `dartKind`: across a dart lies the exterior, in the section of the dart; a relator cell; a
  selected region; or else the face itself.
* `SameSide`: two consecutive darts of a walk lie on one side: one kind, one selected region,
  consecutive on `∂Δ`, or the walk across runs back.
* `baseOf`: the walk starts at the first dart of `∂Δ` if it passes it.
* `groupsOf`: the maximal runs of `SameSide` darts.  `sidesOf`: the runs, with the runs along
  selected regions cut into chunks of length `ε`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

namespace GloballyDistinguishedSectionFamily

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-! ## Definitions -/

open Classical in
/-- The position of a dart on the oriented outer boundary. -/
noncomputable def outerPos (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (d : S.diagram.toCombMap.Dart) : ℕ :=
  (outerDarts S.diagram).idxOf d

open Classical in
/-- What lies across a dart: the exterior, in the section of the dart; a relator cell; a
selected region; or else the face itself. -/
noncomputable def dartKind (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (d : S.diagram.toCombMap.Dart) : OsinLemma94SideClass S.diagram.rCellCount :=
  if S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = S.diagram.outerFace then
    .boundary (PolygonList.sectionIndex cuts.cut (S.outerPos d))
  else if h : ∃ j : Fin S.diagram.rCellCount,
      (cell S.diagram j).face = S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) then
    .cell (Classical.choose h)
  else if ∃ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1 then
    .short
  else .cutting

open Classical in
/-- The selected region across a dart, if any. -/
noncomputable def regionOf (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (d : S.diagram.toCombMap.Dart) : Option (RegionCandidate D eps S.diagram) :=
  if h : ∃ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1 then
    some (Classical.choose h)
  else none

/-- Two consecutive darts of a walk lie on one side. -/
def SameSide (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (e e' : S.diagram.toCombMap.Dart) : Prop :=
  S.dartKind e = S.dartKind e' ∧
    (S.dartKind e = .short → S.regionOf e = S.regionOf e') ∧
    (∀ j, S.dartKind e = .boundary j → S.outerPos e' = S.outerPos e + 1) ∧
    (S.dartKind e ≠ .short → (∀ j, S.dartKind e ≠ .boundary j) →
      S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha e') = S.diagram.toCombMap.alpha e)

open Classical in
/-- The base of the walk of a face: the first dart of the oriented outer boundary. -/
noncomputable def baseOf (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) : ℕ :=
  (outerDarts S.diagram).head?.elim 0 fun e => (S.diagram.faceBoundary f).darts.idxOf e

open Classical in
/-- The maximal runs of darts on one side, on the walk from its base. -/
noncomputable def groupsOf (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) : List (List S.diagram.toCombMap.Dart) :=
  ((S.diagram.faceBoundary f).darts.rotate (S.baseOf f)).splitBy
    fun e e' => decide (S.SameSide e e')

/-- The kind of a side, read at its first dart. -/
noncomputable def sideKind (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    List S.diagram.toCombMap.Dart → OsinLemma94SideClass S.diagram.rCellCount
  | [] => .short
  | d :: _ => S.dartKind d

open Classical in
/-- A run along a selected region is cut into chunks of length `ε`. -/
noncomputable def splitSide (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (g : List S.diagram.toCombMap.Dart) : List (List S.diagram.toCombMap.Dart) :=
  if S.sideKind g = .short then PolygonList.chunks eps g else [g]

/-- The sides of the walk of a face. -/
noncomputable def sidesOf (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) : List (List S.diagram.toCombMap.Dart) :=
  (S.groupsOf f).flatMap S.splitSide

/-! ## What lies across a dart -/

variable (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)

theorem face_alpha_of_dartKind_boundary {d : S.diagram.toCombMap.Dart} {j : ℕ}
    (h : S.dartKind d = .boundary j) :
    S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = S.diagram.outerFace ∧
      j = PolygonList.sectionIndex cuts.cut (S.outerPos d) := by
  classical
  unfold dartKind at h
  by_cases h1 : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = S.diagram.outerFace
  · rw [if_pos h1] at h
    exact ⟨h1, (OsinLemma94SideClass.boundary.inj h).symm⟩
  · rw [if_neg h1] at h
    by_cases h2 : ∃ j : Fin S.diagram.rCellCount,
        (cell S.diagram j).face = S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)
    · rw [dif_pos h2] at h
      cases h
    · rw [dif_neg h2] at h
      by_cases h3 : ∃ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1
      · rw [if_pos h3] at h
        cases h
      · rw [if_neg h3] at h
        cases h

theorem face_alpha_of_dartKind_cell {d : S.diagram.toCombMap.Dart} {j : Fin S.diagram.rCellCount}
    (h : S.dartKind d = .cell j) :
    (cell S.diagram j).face = S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) := by
  classical
  unfold dartKind at h
  by_cases h1 : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = S.diagram.outerFace
  · rw [if_pos h1] at h
    cases h
  · rw [if_neg h1] at h
    by_cases h2 : ∃ j : Fin S.diagram.rCellCount,
        (cell S.diagram j).face = S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)
    · rw [dif_pos h2] at h
      rw [← OsinLemma94SideClass.cell.inj h]
      exact Classical.choose_spec h2
    · rw [dif_neg h2] at h
      by_cases h3 : ∃ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1
      · rw [if_pos h3] at h
        cases h
      · rw [if_neg h3] at h
        cases h

theorem exists_region_of_dartKind_short {d : S.diagram.toCombMap.Dart}
    (h : S.dartKind d = .short) :
    ∃ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1 := by
  classical
  unfold dartKind at h
  by_cases h1 : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = S.diagram.outerFace
  · rw [if_pos h1] at h
    cases h
  · rw [if_neg h1] at h
    by_cases h2 : ∃ j : Fin S.diagram.rCellCount,
        (cell S.diagram j).face = S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)
    · rw [dif_pos h2] at h
      cases h
    · rw [dif_neg h2] at h
      by_cases h3 : ∃ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1
      · exact h3
      · rw [if_neg h3] at h
        cases h

theorem unselected_of_dartKind_cutting {d : S.diagram.toCombMap.Dart}
    (h : S.dartKind d = .cutting) :
    S.UnselectedGFace (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)) := by
  classical
  unfold dartKind at h
  by_cases h1 : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = S.diagram.outerFace
  · rw [if_pos h1] at h
    cases h
  · rw [if_neg h1] at h
    by_cases h2 : ∃ j : Fin S.diagram.rCellCount,
        (cell S.diagram j).face = S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)
    · rw [dif_pos h2] at h
      cases h
    · rw [dif_neg h2] at h
      by_cases h3 : ∃ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1
      · rw [if_pos h3] at h
        cases h
      · refine ⟨h1, fun C hC hface => ?_, fun a ha hmem => h3 ⟨a, ha, hmem⟩⟩
        obtain ⟨n, rfl⟩ := List.get_of_mem hC
        exact h2 ⟨n, hface⟩

/-- The region across a dart is the region containing the face across it. -/
theorem regionOf_eq_some {d : S.diagram.toCombMap.Dart} {a : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family)
    (hd : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1) :
    S.regionOf d = some a := by
  classical
  have h : ∃ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1 :=
    ⟨a, ha, hd⟩
  unfold regionOf
  rw [dif_pos h]
  obtain ⟨hmem, hface⟩ := Classical.choose_spec h
  by_contra hne
  have hne' : Classical.choose h ≠ a := fun heq => hne (congrArg some heq)
  exact Finset.disjoint_left.mp (S.pairwise _ hmem a ha hne') hface hd

theorem regionOf_spec {d : S.diagram.toCombMap.Dart} {a : RegionCandidate D eps S.diagram}
    (h : S.regionOf d = some a) :
    a ∈ S.family ∧ S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1 := by
  classical
  unfold regionOf at h
  by_cases hex : ∃ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1
  · rw [dif_pos hex] at h
    rw [← Option.some_inj.mp h]
    exact Classical.choose_spec hex
  · rw [dif_neg hex] at h
    cases h

/-! ## The oriented outer boundary -/

theorem outerDarts_isChain :
    (outerDarts S.diagram).IsChain fun x y =>
      S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha y) = S.diagram.toCombMap.alpha x := by
  have hinv : ∀ x, S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha x) = x :=
    S.diagram.toCombMap.alpha_involutive
  unfold outerDarts
  rw [List.isChain_map, List.isChain_reverse]
  refine (S.diagram.faceBoundary S.diagram.outerFace).chain.imp_of_mem_imp fun a b _ _ h => ?_
  simp only [hinv]
  exact h

theorem outerDarts_ne_nil : outerDarts S.diagram ≠ [] := by
  unfold outerDarts
  simpa using (S.diagram.faceBoundary S.diagram.outerFace).nonempty

theorem outerDarts_closes :
    S.diagram.toCombMap.facePerm
        (S.diagram.toCombMap.alpha ((outerDarts S.diagram).head S.outerDarts_ne_nil)) =
      S.diagram.toCombMap.alpha ((outerDarts S.diagram).getLast S.outerDarts_ne_nil) := by
  have hinv : ∀ x, S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha x) = x :=
    S.diagram.toCombMap.alpha_involutive
  simp only [outerDarts, List.head_map, List.head_reverse, List.getLast_map, List.getLast_reverse,
    hinv]
  exact (S.diagram.faceBoundary S.diagram.outerFace).closes

theorem outerDarts_nodup : (outerDarts S.diagram).Nodup :=
  (List.nodup_reverse.mpr (S.diagram.faceBoundary S.diagram.outerFace).nodup).map
    S.diagram.toCombMap.alpha_involutive.injective

theorem mem_outerDarts {d : S.diagram.toCombMap.Dart}
    (h : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = S.diagram.outerFace) :
    d ∈ outerDarts S.diagram :=
  List.mem_map.mpr ⟨S.diagram.toCombMap.alpha d,
    List.mem_reverse.mpr (((S.diagram.faceBoundary _).mem_iff _).mpr h),
    S.diagram.toCombMap.alpha_involutive d⟩

theorem length_outerDarts : (outerDarts S.diagram).length = Delta.boundaryWord.length := by
  rw [← S.equiv.boundaryWord_eq, ← dartWord_outerDarts, dartWord, List.length_map]

/-- A chain that runs back across itself. -/
theorem runsBackAcross_of_isChain {path : List S.diagram.toCombMap.Dart}
    (h : path.IsChain fun x y =>
      S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha y) = S.diagram.toCombMap.alpha x) :
    S.RunsBackAcross path := by
  intro j e e' he he'
  rw [getElem?_eq_some_iff] at he he'
  obtain ⟨_, rfl⟩ := he
  obtain ⟨hj', rfl⟩ := he'
  exact List.isChain_iff_getElem.mp h j hj'

#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.unselected_of_dartKind_cutting
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.regionOf_eq_some
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.outerDarts_closes
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.length_outerDarts
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.runsBackAcross_of_isChain

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen
