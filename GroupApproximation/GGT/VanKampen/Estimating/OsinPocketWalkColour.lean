import GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring
import GroupApproximation.GGT.VanKampen.FaceSetDualReach
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketSectionFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerExterior
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket walk carries one colour

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

`ClosedWalkFaceColouring.exists_boundaryCycle_of_orient` makes a closed walk the boundary cycle of
a colour class, provided that every two-colouring changing colour exactly across the walk gives the
faces of all walk darts one colour.  This module proves that hypothesis for the pocket walk
`s_1 t_1 s_2 t_2` of two exterior regions `x`, `y` of a cell `Π`.

* The faces of `x` are joined by edges inside `x`, and no walk dart has both of its faces in `x`,
  so `x` has one colour.  Likewise `y`.
* The walk crosses from `Π` into `x` at a dart of the source arc of `x`, and into `y` at one of
  `y`.  So `x` and `y` both have the colour opposite to `Π`.  At the first dart of the target arc
  of `x` it crosses from `x` into the outer face, so the outer face has the colour of `Π`.
* Every walk dart has its face in `x` or `y`, or crosses into `Π` or the outer face, so its face
  has the colour of `x`.

* `PocketWalkColour.orient_of_sides`: the last step, for any closed walk.
* `PocketWalkColour.walk_orient`: the pocket walk of two exterior regions carries one colour.
* `PocketWalkColourStatement` / `pocketWalkColour`: the same for the pocket walk given by
  `PocketWalk.exists_of_exteriorAt`.

## Manuscript status

Infrastructure for `thm:hull` ("Hull's small cancellation theorem", through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Embedded HullSC WordMetric SimpleClosedWalkSides

universe u w v

namespace PocketWalkColour

/-- **Orientation from two sides.**  Let the faces in `faces` and the other faces meet exactly
across the edges of the closed walk `w`.  Let every walk dart have its face in `A` or cross into a
face of `B`, let every face of `A` and every face of `B` get different colours, and let `A` and
`B` be nonempty.  Then the faces of all walk darts get one colour. -/
theorem orient_of_sides {M : CombMap.{u}} {w : List M.Dart} {faces : Finset M.Face}
    (hcol : ∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔ walkKeep M w d)
    {A B : M.Face → Prop}
    (hcover : ∀ d ∈ w, A (M.faceOf d) ∨ B (M.faceOf (M.alpha d)))
    (hsep : ∀ f g, A f → B g → ¬ (f ∈ faces ↔ g ∈ faces))
    {f₀ g₀ : M.Face} (hf₀ : A f₀) (hg₀ : B g₀) :
    ∀ d ∈ w, ∀ e ∈ w, (M.faceOf d ∈ faces ↔ M.faceOf e ∈ faces) := by
  have hB : ∀ g, B g → (g ∈ faces ↔ g₀ ∈ faces) := fun g hg => by
    have h₁ := hsep f₀ g hf₀ hg
    have h₂ := hsep f₀ g₀ hf₀ hg₀
    tauto
  have hone : ∀ d ∈ w, (M.faceOf d ∈ faces ↔ ¬ g₀ ∈ faces) := fun d hd => by
    rcases hcover d hd with hA | hBd
    · have h := hsep _ g₀ hA hg₀
      tauto
    · have h := (hcol d).mpr (Or.inl hd)
      have h' := hB _ hBd
      tauto
  intro d hd e he
  exact (hone d hd).trans (hone e he).symm

/-- Two propositions each disagreeing with a third agree with each other. -/
theorem iff_of_not_iff_of_not_iff {a b c : Prop} (ha : ¬ (a ↔ c)) (hb : ¬ (b ↔ c)) : a ↔ b := by
  tauto

/-- **A region has one colour.**  Let a face set of a diagram have a boundary cycle, and let no
walk dart have both its face and the face across it in the set.  Then a two-colouring changing
colour exactly across the walk gives all faces of the set one colour. -/
theorem mem_iff_of_faceSetBoundary {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
    {w : List Delta.toCombMap.Dart} {faces R : Finset Delta.toCombMap.Face}
    (hcol : ∀ d, ¬ (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ faces ↔
      Delta.toCombMap.faceOf d ∈ faces) ↔ walkKeep Delta.toCombMap w d)
    (boundary : FaceSetBoundary Delta R)
    (hoff : ∀ e ∈ w, Delta.toCombMap.faceOf e ∈ R →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha e) ∉ R)
    {f g : Delta.toCombMap.Face} (hf : f ∈ R) (hg : g ∈ R) :
    f ∈ faces ↔ g ∈ faces := by
  refine ClosedWalkFaceColouring.mem_iff_of_eqvGen hcol ?_ (dualFaces_connected boundary hf hg)
  rintro f' g' ⟨hf', hg', d, rfl, rfl⟩
  refine ⟨d, rfl, rfl, ?_⟩
  rintro (hd | hd)
  · exact hoff d hd hf' hg'
  · refine hoff _ hd hg' ?_
    rw [Delta.toCombMap.alpha_involutive d]
    exact hf'

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- An exterior region of the cell `i` is selected, has source `i` and targets the outer
boundary. -/
theorem mem_exteriorAt (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {x : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i) :
    x ∈ S.family ∧ x.2.source = i ∧ x.2.target = none := by
  obtain ⟨hxK, hxi⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxS, hxt⟩ := Finset.mem_filter.mp hxK
  refine ⟨hxS, hxi, ?_⟩
  cases h : x.2.target with
  | none => rfl
  | some _ => simp [h] at hxt

/-- An exterior region of the cell `i` has a source dart: a dart of `Π_i` crossed into the
region. -/
theorem exists_sourceDart (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {x : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i) :
    ∃ s ∈ x.2.sourceArc.darts, S.diagram.toCombMap.faceOf s = (cell S.diagram i).face ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha s) ∈ x.1 := by
  obtain ⟨hxS, hxi, -⟩ := mem_exteriorAt S hx
  obtain ⟨s, hs⟩ := x.2.sourceArc.exists_mem_darts (S.nondegenerate x hxS).1
  refine ⟨s, hs, ?_, x.2.faceOf_alpha_mem_of_mem_sourceArc s hs⟩
  rw [← hxi]
  exact faceOf_of_mem_cellDarts (x.2.sourceArc.mem_cycle_of_mem_darts hs)

/-- The source cell of an exterior region is not a face of the region. -/
theorem cell_face_not_mem (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {x : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i) :
    (cell S.diagram i).face ∉ x.1 := by
  obtain ⟨s, hs, hsface, -⟩ := exists_sourceDart S hx
  have hrev : S.diagram.toCombMap.alpha s ∈ x.2.sourceArc.reverseDarts :=
    List.mem_map.mpr ⟨s, List.mem_reverse.mpr hs, rfl⟩
  have hcycle : S.diagram.toCombMap.alpha s ∈ x.2.boundary.cycle := by
    rw [x.2.boundary_decomposition]
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hrev))
  have h := ((x.2.boundary.cycle_mem_iff _).mp hcycle).2
  rw [S.diagram.toCombMap.alpha_involutive s, hsface] at h
  exact h

/-- **The four kinds of pocket walk dart.**  A dart of the pocket walk is a boundary dart of `x`
(the side `s_2`), a boundary dart of `y` (the side `s_1`), a dart crossing into the source cell
(the arc `t_1`), or a dart crossing into the outer face (the arc `t_2`). -/
theorem walk_cases {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ} {i : Fin X.rCellCount}
    {x y : RegionCandidate D eps X} (K : PocketWalk D eps X lo hi) (hsource : K.source = i)
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide)
    {e : X.toCombMap.Dart} (he : e ∈ K.walk) :
    (X.toCombMap.faceOf e ∈ x.1 ∧ X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ x.1) ∨
      (X.toCombMap.faceOf e ∈ y.1 ∧ X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ y.1) ∨
      X.toCombMap.faceOf (X.toCombMap.alpha e) = (cell X i).face ∨
      X.toCombMap.faceOf (X.toCombMap.alpha e) = X.outerFace := by
  simp only [PocketWalk.walk, List.mem_append] at he
  rcases he with ((he | he) | he) | he
  · rw [hfirst] at he
    have hcycle : e ∈ y.2.boundary.cycle := by
      rw [y.2.boundary_decomposition]
      simp only [List.mem_append]
      exact Or.inr he
    exact Or.inr (Or.inl ((y.2.boundary.cycle_mem_iff e).mp hcycle))
  · simp only [invDarts, List.mem_map, List.mem_reverse] at he
    obtain ⟨g, hg, rfl⟩ := he
    refine Or.inr (Or.inr (Or.inl ?_))
    rw [X.toCombMap.alpha_involutive g, ← hsource]
    exact faceOf_of_mem_cellDarts (K.sourceArc.mem_cycle_of_mem_darts hg)
  · rw [hsecond] at he
    have hcycle : e ∈ x.2.boundary.cycle := by
      rw [x.2.boundary_decomposition]
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr he))
    exact Or.inl ((x.2.boundary.cycle_mem_iff e).mp hcycle)
  · exact Or.inr (Or.inr (Or.inr
      (faceOf_alpha_of_mem_targetArc_none X none K.targetArc rfl he)))

/-- The first dart of the target arc of an exterior region `x` lies on a boundary arc starting
where the target arc of `x` starts. -/
theorem exists_targetDart_mem (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {lo hi : ℕ} {x : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i) (K : PocketWalk D eps S.diagram lo hi)
    (hstart : K.targetArc.start.1 = x.2.targetArc.start.1) :
    ∃ e ∈ x.2.targetArc.darts, e ∈ K.targetArc.darts := by
  obtain ⟨hxS, -, hxt⟩ := mem_exteriorAt S hx
  obtain ⟨t, hts, htl, htd⟩ :=
    CyclicArc.exists_transport (targetDarts S.diagram) hxt x.2.targetArc
  have hrot : t.rotated = K.targetArc.rotated := by
    rw [CyclicArc.rotated_eq_rotate, CyclicArc.rotated_eq_rotate, hts, hstart]
    rfl
  have hne : K.targetArc.rotated ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [K.targetArc.rotated_length]
    exact lt_of_lt_of_le K.targetArc_pos K.targetArc.length_le
  obtain ⟨e, r, hr⟩ := List.exists_cons_of_ne_nil hne
  have hmem : ∀ n, 0 < n → e ∈ (e :: r).take n := fun n hn => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    simp
  refine ⟨e, ?_, ?_⟩
  · rw [← htd]
    show e ∈ t.rotated.take t.length
    rw [hrot, hr]
    exact hmem _ (htl ▸ (S.nondegenerate x hxS).2)
  · show e ∈ K.targetArc.rotated.take K.targetArc.length
    rw [hr]
    exact hmem _ K.targetArc_pos

/-- **The pocket walk carries one colour** (parity route, step (C)).  Let `x`, `y` be distinct
exterior regions of the cell `i`, and let `K` be a pocket walk with first side the left side of
`y`, second side the right side of `x`, source arc spanning the source arcs of `x` and `y`, and
target arc starting where the target arc of `x` starts.  Then every two-colouring of the faces
changing colour exactly across the walk gives the faces of all walk darts one colour. -/
theorem walk_orient (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {lo hi : ℕ} {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i)
    (hy : y ∈ RegionCandidate.exteriorAt S.family i) (hxy : x ≠ y)
    (K : PocketWalk D eps S.diagram lo hi) (hsource : K.source = i)
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide)
    (hsourceArc : ∃ Gap : CyclicArc (cellDarts S.diagram i),
      K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts)
    (hstart : K.targetArc.start.1 = x.2.targetArc.start.1)
    {faces : Finset S.diagram.toCombMap.Face}
    (hcol : ∀ d, ¬ (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ faces ↔
      S.diagram.toCombMap.faceOf d ∈ faces) ↔ walkKeep S.diagram.toCombMap K.walk d) :
    ∀ d ∈ K.walk, ∀ e ∈ K.walk,
      (S.diagram.toCombMap.faceOf d ∈ faces ↔ S.diagram.toCombMap.faceOf e ∈ faces) := by
  obtain ⟨hxS, -, hxt⟩ := mem_exteriorAt S hx
  obtain ⟨hyS, -, -⟩ := mem_exteriorAt S hy
  have hdisj : Disjoint x.1 y.1 := S.pairwise x hxS y hyS hxy
  have hPx := cell_face_not_mem S hx
  have hPy := cell_face_not_mem S hy
  -- No walk dart lies inside `x` or inside `y`.
  have hoffx : ∀ e ∈ K.walk, S.diagram.toCombMap.faceOf e ∈ x.1 →
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e) ∉ x.1 := by
    intro e he hex
    rcases walk_cases K hsource hfirst hsecond he with h | h | h | h
    · exact h.2
    · exact absurd h.1 (Finset.disjoint_left.mp hdisj hex)
    · rw [h]
      exact hPx
    · rw [h]
      exact fun hmem => (x.2.boundary.all_gCells _ hmem).1 rfl
  have hoffy : ∀ e ∈ K.walk, S.diagram.toCombMap.faceOf e ∈ y.1 →
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e) ∉ y.1 := by
    intro e he hey
    rcases walk_cases K hsource hfirst hsecond he with h | h | h | h
    · exact absurd hey (Finset.disjoint_left.mp hdisj h.1)
    · exact h.2
    · rw [h]
      exact hPy
    · rw [h]
      exact fun hmem => (y.2.boundary.all_gCells _ hmem).1 rfl
  have hxcol : ∀ f ∈ x.1, ∀ g ∈ x.1, (f ∈ faces ↔ g ∈ faces) := fun f hf g hg =>
    mem_iff_of_faceSetBoundary hcol x.2.boundary hoffx hf hg
  have hycol : ∀ f ∈ y.1, ∀ g ∈ y.1, (f ∈ faces ↔ g ∈ faces) := fun f hf g hg =>
    mem_iff_of_faceSetBoundary hcol y.2.boundary hoffy hf hg
  -- The walk crosses from `Π_i` into `x` and into `y`.
  obtain ⟨Gap, hgap⟩ := hsourceArc
  have hkeep_src : ∀ s ∈ K.sourceArc.darts, walkKeep S.diagram.toCombMap K.walk s := by
    intro s hs
    have h : S.diagram.toCombMap.alpha s ∈ invDarts S.diagram K.sourceArc.darts :=
      List.mem_map.mpr ⟨s, List.mem_reverse.mpr hs, rfl⟩
    refine Or.inr ?_
    simp only [PocketWalk.walk, List.mem_append]
    exact Or.inl (Or.inl (Or.inr h))
  obtain ⟨sx, hsx, hsxface, hsxin⟩ := exists_sourceDart S hx
  obtain ⟨sy, hsy, hsyface, hsyin⟩ := exists_sourceDart S hy
  have hsxK : sx ∈ K.sourceArc.darts := by
    rw [hgap]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hsx)))
  have hsyK : sy ∈ K.sourceArc.darts := by
    rw [hgap]
    exact List.mem_append.mpr (Or.inr hsy)
  have hxP : ¬ (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha sx) ∈ faces ↔
      (cell S.diagram i).face ∈ faces) := by
    rw [← hsxface]
    exact (hcol sx).mpr (hkeep_src sx hsxK)
  have hyP : ¬ (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha sy) ∈ faces ↔
      (cell S.diagram i).face ∈ faces) := by
    rw [← hsyface]
    exact (hcol sy).mpr (hkeep_src sy hsyK)
  -- The walk crosses from `x` into the outer face.
  obtain ⟨t₀, ht₀x, ht₀K⟩ := exists_targetDart_mem S hx K hstart
  have ht₀face : S.diagram.toCombMap.faceOf t₀ ∈ x.1 := by
    have hb := mem_targetBoundaryDarts_of_eq_none S.diagram x.2.target x.2.targetArc hxt ht₀x
    have hcycle : t₀ ∈ x.2.boundary.cycle := by
      rw [x.2.boundary_decomposition]
      simp only [List.mem_append]
      exact Or.inl (Or.inr hb)
    exact ((x.2.boundary.cycle_mem_iff t₀).mp hcycle).1
  have ht₀alpha : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha t₀) =
      S.diagram.outerFace :=
    faceOf_alpha_of_mem_targetArc_none S.diagram x.2.target x.2.targetArc hxt ht₀x
  have hxO : ¬ (S.diagram.toCombMap.faceOf t₀ ∈ faces ↔ S.diagram.outerFace ∈ faces) := by
    have hkeep : walkKeep S.diagram.toCombMap K.walk t₀ := by
      refine Or.inl ?_
      simp only [PocketWalk.walk, List.mem_append]
      exact Or.inr ht₀K
    rw [← ht₀alpha]
    exact fun h => (hcol t₀).mpr hkeep h.symm
  refine orient_of_sides hcol (A := fun f => f ∈ x.1 ∨ f ∈ y.1)
    (B := fun g => g = (cell S.diagram i).face ∨ g = S.diagram.outerFace) ?_ ?_
    (Or.inl hsxin) (Or.inl rfl)
  · intro e he
    rcases walk_cases K hsource hfirst hsecond he with h | h | h | h
    · exact Or.inl (Or.inl h.1)
    · exact Or.inl (Or.inr h.1)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro f g hf (rfl | rfl)
    · rcases hf with hf | hf
      · exact fun h => hxP ((hxcol f hf _ hsxin).symm.trans h)
      · exact fun h => hyP ((hycol f hf _ hsyin).symm.trans h)
    · rcases hf with hf | hf
      · exact fun h => hxO ((hxcol f hf _ ht₀face).symm.trans h)
      · exact fun h => hxO ((hxcol _ hsxin _ ht₀face).symm.trans
          ((iff_of_not_iff_of_not_iff hyP hxP).symm.trans ((hycol f hf _ hsyin).symm.trans h)))

end Pocket

end PocketWalkColour

/-- **The pocket walk of two exterior regions carries one colour** (parity route, step (C)).
Two distinct exterior regions of the cell `i` to the section `j` give the pocket walk of
`PocketWalk.exists_of_exteriorAt`, and every two-colouring of the faces changing colour exactly
across that walk gives the faces of all walk darts one colour. -/
def PocketWalkColourStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {a b : RegionCandidate D eps S.diagram},
    a ∈ RegionCandidate.exteriorAt S.family i → b ∈ RegionCandidate.exteriorAt S.family i →
      a ≠ b → RegionCandidate.TargetsSectionIndex cuts j a →
      RegionCandidate.TargetsSectionIndex cuts j b →
      ∃ (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
        (x y : RegionCandidate D eps S.diagram), (x = a ∧ y = b ∨ x = b ∧ y = a) ∧
        K.source = i ∧ K.firstSide = y.2.leftSide ∧ K.secondSide = x.2.rightSide ∧
        (∃ Gap : CyclicArc (cellDarts S.diagram i),
          K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts) ∧
        K.targetArc.start.1 = x.2.targetArc.start.1 ∧
        K.targetArc.start.1 + K.targetArc.length =
          y.2.targetArc.start.1 + y.2.targetArc.length ∧
        ∀ faces : Finset S.diagram.toCombMap.Face,
          (∀ d, ¬ (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ faces ↔
            S.diagram.toCombMap.faceOf d ∈ faces) ↔ walkKeep S.diagram.toCombMap K.walk d) →
          ∀ d ∈ K.walk, ∀ e ∈ K.walk,
            (S.diagram.toCombMap.faceOf d ∈ faces ↔ S.diagram.toCombMap.faceOf e ∈ faces)

theorem pocketWalkColour : PocketWalkColourStatement.{u, w, v} := by
  intro G _ Lambda W D eps lambda c Delta cuts S i j a b ha hb hab hja hjb
  obtain ⟨K, x, y, hxy, hsrc, hfirst, hsecond, hgap, hstart, hend⟩ :=
    PocketWalk.exists_of_exteriorAt S ha hb hab hja hjb
  have hmem : x ∈ RegionCandidate.exteriorAt S.family i ∧
      y ∈ RegionCandidate.exteriorAt S.family i ∧ x ≠ y := by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hb, hab⟩
    · exact ⟨hb, ha, hab.symm⟩
  exact ⟨K, x, y, hxy, hsrc, hfirst, hsecond, hgap, hstart, hend, fun faces hcol =>
    PocketWalkColour.walk_orient S hmem.1 hmem.2.1 hmem.2.2 K hsrc hfirst hsecond hgap hstart
      hcol⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalkColour.orient_of_sides
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalkColour.iff_of_not_iff_of_not_iff
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalkColour.mem_iff_of_faceSetBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalkColour.mem_exteriorAt
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalkColour.exists_sourceDart
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalkColour.cell_face_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalkColour.walk_cases
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalkColour.exists_targetDart_mem
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalkColour.walk_orient
#audit_closed_axioms GroupApproximation.GGT.VanKampen.pocketWalkColour
