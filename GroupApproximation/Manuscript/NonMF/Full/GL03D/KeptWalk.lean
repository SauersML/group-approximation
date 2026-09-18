import GroupApproximation.Manuscript.NonMF.Full.GL03C.KeptArcs
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The sub-arc region move from a noncrossing kept sub-walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  This is infrastructure for `thm:hull` in `non_mf_groups_exist.tex`
(around line 2121).

`GL06f.RoseRegionMoveSubArcStatement` asks for a colouring `z` of darts.  This module builds `z`
from a choice `q` of boundary darts to keep.  Suppose the kept list `B = K.boundary.cycle.filter q`
is a noncrossing closed walk.  Then the Jordan-curve theorem `isBoundaryDart_sideFaces_iff`
makes `B` the boundary of its side `K' = sideFaces B`, and the colouring
`z x := (faceOf x ∈ K.faces xor faceOf x ∈ K')` does the job:

* `sideColour`, `sideColour_step`: `z` is constant along face class steps of the old cycle.
* `sideColour_ind`: `z` never flips both sides of an old boundary edge.
* `movePred_sideColour_iff`: on the old cycle the kept darts of `z` are exactly those of `B`.
* `flipFaces_sideColour`: the moved face set is `K'`.
* `regionMove_of_colour`, `regionMove_of_keptWalk`: the full conclusion of
  `GL06f.RoseRegionMoveSubArcStatement`, with the listing tail from `GL03C.regionMove_tail`.
* `KeptSubwalkStatement`, `roseRegionMoveSubArc_of_keptSubwalk`: the remaining planar core
  (existence of `q`) and the reduction of the sub-arc region move to it.

Everything here is unconditional.  `KeptSubwalkStatement` is an internal combinatorial statement,
not a literature result.  This module certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL03D

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

section Colour

open Classical in
/-- **The side colouring** (for `thm:hull`): a dart is flipped when its face changes membership
between the old face set `faces` and the new face set `faces'`. -/
noncomputable def sideColour (M : CombMap.{v}) (faces faces' : Finset M.Face) (x : M.Dart) :
    Bool :=
  if (M.faceOf x ∈ faces ↔ M.faceOf x ∈ faces') then false else true

theorem sideColour_eq_false_iff {M : CombMap.{v}} {faces faces' : Finset M.Face} {x : M.Dart} :
    sideColour M faces faces' x = false ↔ (M.faceOf x ∈ faces ↔ M.faceOf x ∈ faces') := by
  unfold sideColour
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => by trivial⟩
  · exact ⟨fun h' => nomatch h', fun h' => absurd h' h⟩

/-- Two booleans with the same `false` fibre are equal. -/
theorem bool_eq_of_eq_false_iff {a b : Bool} (h : a = false ↔ b = false) : a = b := by
  cases a with
  | false => exact (h.mp rfl).symm
  | true =>
    cases b with
    | false => exact h.mpr rfl
    | true => rfl

theorem sideColour_congr {M : CombMap.{v}} {faces faces' : Finset M.Face} {x y : M.Dart}
    (h₁ : M.faceOf x ∈ faces ↔ M.faceOf y ∈ faces)
    (h₂ : M.faceOf x ∈ faces' ↔ M.faceOf y ∈ faces') :
    sideColour M faces faces' x = sideColour M faces faces' y := by
  apply bool_eq_of_eq_false_iff
  rw [sideColour_eq_false_iff, sideColour_eq_false_iff, h₁, h₂]

/-- Across an edge off the boundary cycle of a face set, face membership does not change. -/
theorem mem_iff_mem_alpha_of_not_mem {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    {x : M.Dart} (hx : x ∉ c) (hax : M.alpha x ∉ c) :
    M.faceOf x ∈ faces ↔ M.faceOf (M.alpha x) ∈ faces := by
  constructor
  · intro h
    by_contra h'
    exact hx ((hc x).mpr
      (show M.faceOf x ∈ faces ∧ M.faceOf (M.alpha x) ∉ faces from ⟨h, h'⟩))
  · intro h
    by_contra h'
    have hb : Surgery.MapCollapse.IsBoundaryDart M faces (M.alpha x) := by
      show M.faceOf (M.alpha x) ∈ faces ∧ M.faceOf (M.alpha (M.alpha x)) ∉ faces
      rw [M.alpha_involutive x]
      exact ⟨h, h'⟩
    exact hax ((hc (M.alpha x)).mpr hb)

variable {M : CombMap.{v}} {faces faces' : Finset M.Face} {c B : List M.Dart}

/-- **The side colouring is constant on face classes** of the old boundary cycle `c`, when the
new boundary `B` is part of `c`. -/
theorem sideColour_step (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    (hB : ∀ d, d ∈ B ↔ Surgery.MapCollapse.IsBoundaryDart M faces' d)
    (hsub : ∀ d ∈ B, d ∈ c) (x y : M.Dart)
    (h : CombMap.FaceClassStep M (walkKeep M c) x y) :
    sideColour M faces faces' x = sideColour M faces faces' y := by
  rcases h with rfl | ⟨hkeep, rfl⟩
  · apply sideColour_congr
    · rw [M.faceOf_facePerm]
    · rw [M.faceOf_facePerm]
  · have hx : x ∉ c := fun hx => hkeep (Or.inl hx)
    have hax : M.alpha x ∉ c := fun hax => hkeep (Or.inr hax)
    apply sideColour_congr
    · exact mem_iff_mem_alpha_of_not_mem hc hx hax
    · exact mem_iff_mem_alpha_of_not_mem hB (fun h => hx (hsub x h))
        (fun h => hax (hsub (M.alpha x) h))

/-- **The side colouring never flips both sides of an old boundary edge.** -/
theorem sideColour_ind (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    (hB : ∀ d, d ∈ B ↔ Surgery.MapCollapse.IsBoundaryDart M faces' d)
    (hsub : ∀ d ∈ B, d ∈ c) {d : M.Dart} (hd : d ∈ c) :
    sideColour M faces faces' d = false ∨ sideColour M faces faces' (M.alpha d) = false := by
  have hbd : M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces := (hc d).mp hd
  rw [sideColour_eq_false_iff, sideColour_eq_false_iff]
  by_cases h : M.faceOf d ∈ faces'
  · exact Or.inl ⟨fun _ => h, fun _ => hbd.1⟩
  · right
    constructor
    · intro h'
      exact absurd h' hbd.2
    · intro h'
      exfalso
      have hb : Surgery.MapCollapse.IsBoundaryDart M faces' (M.alpha d) := by
        show M.faceOf (M.alpha d) ∈ faces' ∧ M.faceOf (M.alpha (M.alpha d)) ∉ faces'
        rw [M.alpha_involutive d]
        exact ⟨h', h⟩
      have hm : M.faceOf (M.alpha d) ∈ faces ∧ M.faceOf (M.alpha (M.alpha d)) ∉ faces :=
        (hc (M.alpha d)).mp (hsub (M.alpha d) ((hB (M.alpha d)).mpr hb))
      exact hbd.2 hm.1

/-- **On the old cycle, the side colouring keeps exactly the new boundary darts.** -/
theorem movePred_sideColour_iff
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    (hB : ∀ d, d ∈ B ↔ Surgery.MapCollapse.IsBoundaryDart M faces' d)
    {d : M.Dart} (hd : d ∈ c) :
    GL05b.movePred M (sideColour M faces faces') d = true ↔ d ∈ B := by
  have hbd : M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces := (hc d).mp hd
  rw [GL05b.movePred_eq_true_iff, sideColour_eq_false_iff, sideColour_eq_false_iff, hB d]
  show _ ↔ M.faceOf d ∈ faces' ∧ M.faceOf (M.alpha d) ∉ faces'
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.mp hbd.1, fun h => hbd.2 (h2.mpr h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun _ => h1, fun _ => hbd.1⟩,
      ⟨fun h => absurd h hbd.2, fun h => absurd h h2⟩⟩

/-- **The moved face set of the side colouring is the new face set.** -/
theorem flipFaces_sideColour {keep : M.Dart → Prop}
    (hz : ∀ x y, CombMap.FaceClassStep M keep x y →
      sideColour M faces faces' x = sideColour M faces faces' y) :
    GL06f.flipFaces M faces (sideColour M faces faces') = faces' := by
  ext f
  refine Quotient.inductionOn' f ?_
  intro x
  show M.faceOf x ∈ GL06f.flipFaces M faces (sideColour M faces faces') ↔ M.faceOf x ∈ faces'
  have key := GL06f.mem_flipFaces_iff (faces := faces) hz x
  rw [sideColour_eq_false_iff] at key
  rw [key]
  by_cases hA : M.faceOf x ∈ faces
  · exact ⟨fun h => (h.mp hA).mp hA,
      fun hb => ⟨fun _ => ⟨fun _ => hb, fun _ => hA⟩, fun _ => hA⟩⟩
  · constructor
    · intro h
      by_contra hb
      exact hA (h.mpr ⟨fun ha => absurd ha hA, fun hb' => absurd hb' hb⟩)
    · intro hb
      exact ⟨fun ha => absurd ha hA, fun hab => hab.mpr hb⟩

end Colour

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The sub-arc region move from a colouring that keeps a noncrossing sub-walk**
(Osin Lemma 9.7(b), for `thm:hull`).  A colouring `z` that is constant on face classes, never
flips both sides of a boundary edge, moves `K.faces` to the side of `B = K.boundary.cycle.filter q`
and keeps exactly the darts of `B` gives the conclusion of `GL06f.RoseRegionMoveSubArcStatement`. -/
theorem regionMove_of_colour (K : PocketFaceSet D eps X lo hi) (q z : X.toCombMap.Dart → Bool)
    (hw : IsNoncrossingClosedWalk X.toCombMap (K.boundary.cycle.filter q))
    (hz : ∀ x y, CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) x y → z x = z y)
    (hind : ∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false)
    (hflip : GL06f.flipFaces X.toCombMap K.faces z =
      sideFaces X.toCombMap (K.boundary.cycle.filter q))
    (hpred : ∀ d ∈ K.boundary.cycle, GL05b.movePred X.toCombMap z d = q d)
    (hproper : ∃ y ∈ K.boundary.cycle, q y = false)
    (hout : X.outerFace ∉ sideFaces X.toCombMap (K.boundary.cycle.filter q))
    (hsource : (cell X K.source).face ∉ sideFaces X.toCombMap (K.boundary.cycle.filter q))
    (hkept : ∃ kept : Fin X.rCellCount,
      (cell X kept).face ∈ sideFaces X.toCombMap (K.boundary.cycle.filter q))
    (hsrcBlock : GL05b.IsEndBlock q (invDarts X K.sourceArc.darts))
    (htgtBlock : ∃ i, K.targetArc.darts.filter q = K.targetArc.darts.take i ∨
      (K.targetArc.darts.filter q = K.targetArc.darts.drop i ∧
        K.targetArc.start.1 + i ≤ (outerDarts X).length))
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length) :
    ∃ z : X.toCombMap.Dart → Bool,
      (∀ x y, CombMap.FaceClassStep X.toCombMap
        (walkKeep X.toCombMap K.boundary.cycle) x y → z x = z y) ∧
      (∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false) ∧
      X.outerFace ∉ GL06f.flipFaces X.toCombMap K.faces z ∧
      (∃ y ∈ K.boundary.cycle, GL05b.movePred X.toCombMap z y = false) ∧
      ∃ (source kept : Fin X.rCellCount),
        (cell X source).face ∉ GL06f.flipFaces X.toCombMap K.faces z ∧
        (cell X kept).face ∈ GL06f.flipFaces X.toCombMap K.faces z ∧
        ∃ (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
          (s₁ s₂ : List X.toCombMap.Dart),
          List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
            (K.boundary.cycle.filter (GL05b.movePred X.toCombMap z)) ∧
          IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ∧
          s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
          t₂.start.1 + t₂.length ≤ hi ∧
          t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length := by
  have hfilter : ∀ l : List X.toCombMap.Dart, (∀ d ∈ l, d ∈ K.boundary.cycle) →
      l.filter (GL05b.movePred X.toCombMap z) = l.filter q :=
    fun l hl => List.filter_congr fun d hd => hpred d (hl d hd)
  have hcyc := hfilter K.boundary.cycle (fun _ h => h)
  have hdec := K.decomposition
  have hinv : ∀ d ∈ invDarts X K.sourceArc.darts, d ∈ K.boundary.cycle := by
    intro d hd
    rw [hdec]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hd))
  have htgtSub : ∀ d ∈ K.targetArc.darts, d ∈ K.boundary.cycle := by
    intro d hd
    rw [hdec]
    exact List.mem_append_right _ hd
  have hne : K.boundary.cycle.filter (GL05b.movePred X.toCombMap z) ≠ [] := by
    rw [hcyc]
    exact hw.ne_nil
  have hchain : (K.boundary.cycle.filter (GL05b.movePred X.toCombMap z)).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
    rw [hcyc]
    exact hw.chain
  have hsrcBlock' : GL05b.IsEndBlock (GL05b.movePred X.toCombMap z)
      (invDarts X K.sourceArc.darts) := by
    unfold GL05b.IsEndBlock
    rw [hfilter _ hinv]
    exact hsrcBlock
  have htgtBlock' : ∃ i, K.targetArc.darts.filter (GL05b.movePred X.toCombMap z) =
        K.targetArc.darts.take i ∨
      (K.targetArc.darts.filter (GL05b.movePred X.toCombMap z) = K.targetArc.darts.drop i ∧
        K.targetArc.start.1 + i ≤ (outerDarts X).length) := by
    rw [hfilter _ htgtSub]
    exact htgtBlock
  have htail :=
    GL03C.regionMove_tail K hz hind hne hchain hsrcBlock' htgtBlock' hsrc htgt
  obtain ⟨y, hy, hqy⟩ := hproper
  obtain ⟨kept, hkeptMem⟩ := hkept
  refine ⟨z, hz, hind, ?_, ⟨y, hy, ?_⟩, K.source, kept, ?_, ?_, htail⟩
  · rw [hflip]
    exact hout
  · rw [hpred y hy]
    exact hqy
  · rw [hflip]
    exact hsource
  · rw [hflip]
    exact hkeptMem

/-- **The sub-arc region move from a noncrossing kept sub-walk** (Osin Lemma 9.7(b), for
`thm:hull`).  If the darts of the pocket boundary chosen by `q` form a noncrossing closed walk in
cycle order, whose side avoids the exterior and the source cell and contains some relator cell,
and `q` keeps an end block of each arc and drops some dart, then the side colouring gives the
conclusion of `GL06f.RoseRegionMoveSubArcStatement`. -/
theorem regionMove_of_keptWalk (K : PocketFaceSet D eps X lo hi) (q : X.toCombMap.Dart → Bool)
    (hw : IsNoncrossingClosedWalk X.toCombMap (K.boundary.cycle.filter q))
    (hproper : ∃ y ∈ K.boundary.cycle, q y = false)
    (hout : X.outerFace ∉ sideFaces X.toCombMap (K.boundary.cycle.filter q))
    (hsource : (cell X K.source).face ∉ sideFaces X.toCombMap (K.boundary.cycle.filter q))
    (hkept : ∃ kept : Fin X.rCellCount,
      (cell X kept).face ∈ sideFaces X.toCombMap (K.boundary.cycle.filter q))
    (hsrcBlock : GL05b.IsEndBlock q (invDarts X K.sourceArc.darts))
    (htgtBlock : ∃ i, K.targetArc.darts.filter q = K.targetArc.darts.take i ∨
      (K.targetArc.darts.filter q = K.targetArc.darts.drop i ∧
        K.targetArc.start.1 + i ≤ (outerDarts X).length))
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length) :
    ∃ z : X.toCombMap.Dart → Bool,
      (∀ x y, CombMap.FaceClassStep X.toCombMap
        (walkKeep X.toCombMap K.boundary.cycle) x y → z x = z y) ∧
      (∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false) ∧
      X.outerFace ∉ GL06f.flipFaces X.toCombMap K.faces z ∧
      (∃ y ∈ K.boundary.cycle, GL05b.movePred X.toCombMap z y = false) ∧
      ∃ (source kept : Fin X.rCellCount),
        (cell X source).face ∉ GL06f.flipFaces X.toCombMap K.faces z ∧
        (cell X kept).face ∈ GL06f.flipFaces X.toCombMap K.faces z ∧
        ∃ (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
          (s₁ s₂ : List X.toCombMap.Dart),
          List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
            (K.boundary.cycle.filter (GL05b.movePred X.toCombMap z)) ∧
          IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ∧
          s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
          t₂.start.1 + t₂.length ≤ hi ∧
          t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length := by
  have hc := K.boundary.cycle_mem_iff
  have hB : ∀ d, d ∈ K.boundary.cycle.filter q ↔
      Surgery.MapCollapse.IsBoundaryDart X.toCombMap
        (sideFaces X.toCombMap (K.boundary.cycle.filter q)) d :=
    fun d => (hw.isBoundaryDart_sideFaces_iff X.planar d).symm
  have hsub : ∀ d ∈ K.boundary.cycle.filter q, d ∈ K.boundary.cycle :=
    fun d hd => (List.mem_filter.mp hd).1
  have hz := sideColour_step hc hB hsub
  refine regionMove_of_colour K q
    (sideColour X.toCombMap K.faces (sideFaces X.toCombMap (K.boundary.cycle.filter q)))
    hw hz (fun d hd => sideColour_ind hc hB hsub hd) (flipFaces_sideColour hz) ?_
    hproper hout hsource hkept hsrcBlock htgtBlock hsrc htgt
  intro d hd
  rw [Bool.eq_iff_iff, movePred_sideColour_iff hc hB hd, List.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hd, h⟩⟩

end Pocket

/-- **The planar core of the sub-arc region move** (Osin Lemma 9.7(b), for `thm:hull`).  In the
rose configuration some choice `q` of boundary darts keeps a noncrossing closed walk in cycle
order, whose side avoids the exterior and the source cell and contains a relator cell, dropping
some dart and keeping an end block of each arc.  This is an internal combinatorial statement
(the existence half of `GL06f.RoseRegionMoveSubArcStatement`), not a literature result. -/
def KeptSubwalkStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      GL06f.AllNonFirstTurnsCrossed K →
        ∃ q : X.toCombMap.Dart → Bool,
          IsNoncrossingClosedWalk X.toCombMap (K.boundary.cycle.filter q) ∧
          (∃ y ∈ K.boundary.cycle, q y = false) ∧
          X.outerFace ∉ sideFaces X.toCombMap (K.boundary.cycle.filter q) ∧
          (cell X K.source).face ∉ sideFaces X.toCombMap (K.boundary.cycle.filter q) ∧
          (∃ kept : Fin X.rCellCount,
            (cell X kept).face ∈ sideFaces X.toCombMap (K.boundary.cycle.filter q)) ∧
          GL05b.IsEndBlock q (invDarts X K.sourceArc.darts) ∧
          ∃ i, K.targetArc.darts.filter q = K.targetArc.darts.take i ∨
            (K.targetArc.darts.filter q = K.targetArc.darts.drop i ∧
              K.targetArc.start.1 + i ≤ (outerDarts X).length)

/-- **The sub-arc region move from its planar core** (for `thm:hull`). -/
theorem roseRegionMoveSubArc_of_keptSubwalk (h : KeptSubwalkStatement.{u, w, v}) :
    GL06f.RoseRegionMoveSubArcStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hLA hlet K hwalk hft hsrc htgt hpin hrose
  obtain ⟨q, hw, hproper, hout, hsource, hkept, hsrcBlock, htgtBlock⟩ :=
    h D eps X lo hi hLA hlet K hwalk hft hsrc htgt hpin hrose
  exact regionMove_of_keptWalk K q hw hproper hout hsource hkept hsrcBlock htgtBlock hsrc htgt

end GroupApproximation.Full.GL03D

#audit_axioms GroupApproximation.Full.GL03D.sideColour_step
#audit_axioms GroupApproximation.Full.GL03D.flipFaces_sideColour
#audit_axioms GroupApproximation.Full.GL03D.regionMove_of_colour
#audit_axioms GroupApproximation.Full.GL03D.regionMove_of_keptWalk
#audit_axioms GroupApproximation.Full.GL03D.roseRegionMoveSubArc_of_keptSubwalk
