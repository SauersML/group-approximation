import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Doubling
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellTransport
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchCornerFix
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhi
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the corner refinement at a bad corner (part 1, the corner digon)

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  We prove `BadCornerRefinementStatement`
(`Piece06/Doubling`, gap 5) from the strictly smaller `MonogonCornerStatement` below
(`CornerRefineAssemble.badCornerRefinement_of_monogonCorner`).

## Notation

`K` is a cell pocket of `X` with boundary cycle `c` (no duplicates), in walk order, with distinct
proper cells.  For a dart `z` write `f = face (α z) = face (σ z)` (`faceOf_sigma_eq_alpha`).

## The corner digon (`CornerDigon K z`)

A refinement `R : X → X'` carrying the pocket (`K'` with `c' = c.map R`, same invariants and repeated
visits) in which the rotation step `z ↦ σ z` lifts to `R z ↦ R (σ z)` in `p` steps, all intermediate
darts new, and for some `m < p` the corner face `g = face' (α' (σ'^m (R z)))` is a G-face of `X'` (off
the exterior, off the relator cells), whose old darts are among `α z`, `σ z`; and every G-face of `X`
other than `f` stays a G-face.

## Hypotheses at a corner

(H1) `f ∉ K.faces`.  (H2) `α (σ z)` is not followed by `z` in `c`.

## Case analysis (`cornerDigon_of_monogonCorner`)

* **Monogon** `σ z = α z` (`|f| = 1`): the gap `MonogonCornerStatement`.
* Otherwise `α z ≠ σ z` both lie on the traversal of `f`, so `1 < |f|` (`one_lt_length_of_mem_ne`).
  Pick `wd ∈ {α z, σ z}` on neither arc (`exists_corner_dart`):
  - if `σ z` is on the first arc of cell `i`, then `α z` is not on the first arc (else both are
    consecutive on the proper arc, so `α (σ z)` precedes `z` in `c`: `cycle_next_of_firstArc`,
    contradicting (H2)), and not on the second arc (its face would be both cells, `i = j`);
  - symmetric for the second arc; otherwise take `σ z`.
  Let `k` be the position of `wd` in the traversal of `f`.
  - `f ≠ outer`: `CellPocketFaceSet.faceEdgeDoubling` at `k`; `R = RotationRefinement.edgeInsertion`.
  - `f = outer`: `CellPocketFaceSet.outerSpurThickening` at `k`.
  In both, the split map is `EdgeInsertion.toCombMap M a b` with `a = wd`, `b = facePerm wd`.  The new
  darts are `some none` (before `a`) and `none` (before `b`), and the digon is `[none, embed wd]`.
  - `wd = α z`: lift the step by `exists_sigma_step_lift` (intermediates `none`, `some none`), `m = 0`:
    `α' (embed z) = embed (α z) = embed wd` lies on the digon.
  - `wd = σ z`: `σ' (embed z) = some none` (`sigma_embed_apply`), `σ' (some none) = embed a`, so
    `p = 2`, `m = 1`, and `α' (some none) = none` lies on the digon.
  The digon is not a face image (`faceImage_ne_digon`), hence a G-face; an old dart on it is `wd`
  (`eq_of_faceOf_embed_digon`); faces other than `f` map by the injective `faceImage`
  (`faceOf_embed_of_ne`), and the exterior and cells are images, so G-faces stay G-faces.

## Assembly (`badCornerRefinement_of_monogonCorner`)

Step 1 at `z = e₀`: (H1) since `e₀ ∈ c`; (H2) since otherwise `σ e₀ = α d₀`
(`OuterPinchCornerFix.sigma_eq_of_cycle_next_e₀`).  Get `R₁`, `p₁`, `m₁`, `x₁ = σ₁^m₁ (R₁ e₀)`.

Step 2 in `X₁` at `z₂ = σ₁⁻¹ (R₁ (α d₀))`: (H1) since `face₁ (α₁ z₂) = face₁ (α₁ (R₁ d₀))` and
`R₁ d₀ ∈ c₁`; (H2): otherwise `z₂ = next (R₁ d₀) = R₁ e₀`, so `σ₁ (R₁ e₀) = R₁ (α d₀)` is old; since
the intermediates are new this forces `p₁ = 1` and `σ e₀ = α d₀` (`hone_second`).  Get `R₂`, `p₂`,
`m₂`, `y = σ₂^m₂ (R₂ z₂)`.

Faces: `face₁ (α₁ x₁) ≠ face₁ (α₁ z₂)`: otherwise `R₁ (α d₀)` lies on the first digon, so
`α d₀ ∈ {α e₀, σ e₀}`; `d₀ = e₀` contradicts `next d₀ ≠ d₀` (`|c| ≥ 2`), the other is `hne`.  So the
first digon survives as a G-face of `X₂`.  Sector for `R = R₁.comp R₂`: `x = σ₂^K (R₂ (R₁ e₀)) =
R₂ x₁` with `K` from `lift_pow`, `m = K`; `q = p₂ - m₂`.  New darts: intermediates of `lift_pow` pull
back to intermediates of step 1, and `x` itself is `R₂ x₁` with `0 < m₁ < p₁`.  Corner faces distinct:
if `face₂ (R₂ (α₁ x₁))` is the second digon, `α₁ x₁ ∈ {α₁ z₂, σ₁ z₂}`, whose faces are `face₁ (α₁ z₂)`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated Equiv
open scoped Classical

section Lists

variable {α : Type*}

/-- In a duplicate-free list of length at least two, no entry is its own successor. -/
theorem next_ne_self_of_two_le {l : List α} (hl : l.Nodup) (h2 : 2 ≤ l.length) {a : α}
    (ha : a ∈ l) : l.next a ha ≠ a := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  intro h
  have h' : l[(i + 1) % l.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) = l[i] :=
    (List.next_getElem l hl i hi).symm.trans h
  have hmod := (hl.getElem_inj_iff).mp h'
  rcases Nat.lt_or_ge (i + 1) l.length with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hmod
    omega
  · have heq : i + 1 = l.length := by omega
    rw [heq, Nat.mod_self] at hmod
    omega

/-- A list with two distinct members has length at least two. -/
theorem one_lt_length_of_mem_ne {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    1 < l.length := by
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
  · simp at ha
  · rw [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  · exact Nat.succ_lt_succ (Nat.succ_pos _)

end Lists

section Faces

variable (M : CombMap.{v})

/-- The two darts of a corner lie on one face. -/
theorem faceOf_sigma_eq_alpha (z : M.Dart) : M.faceOf (M.sigma z) = M.faceOf (M.alpha z) := by
  have h := M.faceOf_facePerm (M.alpha z)
  rwa [OuterPinchCornerFix.facePerm_alpha] at h

/-- The corner before `y`. -/
theorem faceOf_alpha_sigma_symm (y : M.Dart) :
    M.faceOf (M.alpha (M.sigma.symm y)) = M.faceOf y := by
  have h := faceOf_sigma_eq_alpha M (M.sigma.symm y)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

end Faces

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- A G-face: off the exterior and off the relator cells. -/
abbrev IsGFaceOf (X : DiscDiagram.{u, w, v} W) (g : X.toCombMap.Face) : Prop :=
  g ≠ X.outerFace ∧ ∀ C ∈ X.relatorCells, C.face ≠ g

theorem isGFaceOf_congr {X : DiscDiagram.{u, w, v} W} {g g' : X.toCombMap.Face} (h : g = g')
    (hg : IsGFaceOf X g') : IsGFaceOf X g :=
  h ▸ hg

/-- The invariants of a cell pocket carried by the step. -/
abbrev PocketInvariants {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
    (K : CellPocketFaceSet D eps X i j) : Prop :=
  (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) ∧ K.ClosedWalk ∧ i ≠ j ∧
    K.firstArc.length < (cellDarts X i).length ∧ K.secondArc.length < (cellDarts X j).length

/-- **A G-digon in the corner between `z` and `σ z`**, through a refinement carrying the pocket. -/
abbrev CornerDigon {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
    (K : CellPocketFaceSet D eps X i j) (z : X.toCombMap.Dart) : Prop :=
  ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
    (K' : CellPocketFaceSet D eps X' i' j') (R : RotationRefinement X.toCombMap X'.toCombMap),
    Nonempty (OEquivalentDiscDiagram X X') ∧ PocketInvariants K' ∧
      K'.repeatedVisits = K.repeatedVisits ∧ K'.boundary.cycle = K.boundary.cycle.map R.map ∧
      ∃ p m : ℕ, m < p ∧ (X'.toCombMap.sigma ^ p) (R.map z) = R.map (X.toCombMap.sigma z) ∧
        (∀ t, 0 < t → t < p → ∀ w, (X'.toCombMap.sigma ^ t) (R.map z) ≠ R.map w) ∧
        IsGFaceOf X'
          (X'.toCombMap.faceOf (X'.toCombMap.alpha ((X'.toCombMap.sigma ^ m) (R.map z)))) ∧
        (∀ w, X'.toCombMap.faceOf (R.map w) =
            X'.toCombMap.faceOf (X'.toCombMap.alpha ((X'.toCombMap.sigma ^ m) (R.map z))) →
          w = X.toCombMap.alpha z ∨ w = X.toCombMap.sigma z) ∧
        ∀ w, IsGFaceOf X (X.toCombMap.faceOf w) →
          X.toCombMap.faceOf w ≠ X.toCombMap.faceOf (X.toCombMap.alpha z) →
          IsGFaceOf X' (X'.toCombMap.faceOf (R.map w))

/-- **The isolated gap: a monogon corner face.**  When `σ z = α z`, the corner face of `z` is a
monogon (a one-letter relator cell, a one-letter G-face, or a one-edge exterior); neither
`faceEdgeDoubling` nor `outerSpurThickening` applies (`hlen`), and the library has no cell-pocket
transport of a monogon doubling. -/
def MonogonCornerStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
    (K : CellPocketFaceSet D eps X i j) (z : X.toCombMap.Dart),
    PocketInvariants K → X.toCombMap.faceOf (X.toCombMap.alpha z) ∉ K.faces →
    (¬ ∃ h : X.toCombMap.alpha (X.toCombMap.sigma z) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = z) →
    X.toCombMap.sigma z = X.toCombMap.alpha z → CornerDigon K z

section Arcs

variable {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- A dart of an arc of a cell lies on that cell. -/
theorem faceOf_mem_arc {c : Fin X.rCellCount} (arc : CyclicArc (cellDarts X c))
    {d : X.toCombMap.Dart} (hd : d ∈ arc.darts) :
    X.toCombMap.faceOf d = (Embedded.cell X c).face :=
  ((X.faceBoundary (Embedded.cell X c).face).mem_iff d).mp (arc.mem_cycle_of_mem_darts hd)

theorem invDarts_firstArc_infix (K : CellPocketFaceSet D eps X i j) :
    invDarts X K.firstArc.darts <:+: K.boundary.cycle := by
  rw [K.decomposition]
  exact (List.infix_append K.firstSide _ K.secondSide).trans (List.prefix_append _ _).isInfix

theorem invDarts_secondArc_infix (K : CellPocketFaceSet D eps X i j) :
    invDarts X K.secondArc.darts <:+: K.boundary.cycle := by
  rw [K.decomposition]
  exact (List.suffix_append _ _).isInfix

/-- The boundary cycle of a cell pocket has at least two darts. -/
theorem two_le_cycle_length (K : CellPocketFaceSet D eps X i j) : 2 ≤ K.boundary.cycle.length := by
  have h1 := K.firstArc_pos
  have h2 := K.secondArc_pos
  rw [K.decomposition]
  simp only [List.length_append, invDarts, List.length_map, List.length_reverse,
    CyclicArc.darts_length]
  omega

/-- **Both corner darts on the first arc.** -/
theorem cycle_next_of_firstArc (K : CellPocketFaceSet D eps X i j)
    (hprop : K.firstArc.length < (cellDarts X i).length) {u : X.toCombMap.Dart}
    (ha : X.toCombMap.alpha u ∈ K.firstArc.darts) (hb : X.toCombMap.sigma u ∈ K.firstArc.darts) :
    ∃ h : X.toCombMap.alpha (X.toCombMap.sigma u) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = u := by
  have hcarrier : (cellDarts X i).next (X.toCombMap.alpha u)
      (K.firstArc.mem_cycle_of_mem_darts ha) = X.toCombMap.sigma u :=
    (OuterPinchCornerFix.next_faceBoundary_darts (X.faceBoundary (Embedded.cell X i).face)
      (K.firstArc.mem_cycle_of_mem_darts ha)).trans (OuterPinchCornerFix.facePerm_alpha u)
  have hinf := OuterPinchCornerFix.infix_of_next_of_mem K.firstArc
    (X.faceBoundary (Embedded.cell X i).face).nodup hprop ha hb hcarrier
  have hinf2 := (List.IsInfix.map X.toCombMap.alpha hinf.reverse).trans (invDarts_firstArc_infix K)
  have e : [X.toCombMap.alpha u, X.toCombMap.sigma u].reverse.map X.toCombMap.alpha =
      [X.toCombMap.alpha (X.toCombMap.sigma u), u] := by
    simp [X.toCombMap.alpha_involutive u]
  rw [e] at hinf2
  exact ⟨hinf2.mem (by simp), OuterPinchCornerFix.next_eq_of_infix K.boundary.cycle_nodup hinf2 _⟩

/-- **Both corner darts on the second arc.** -/
theorem cycle_next_of_secondArc (K : CellPocketFaceSet D eps X i j)
    (hprop : K.secondArc.length < (cellDarts X j).length) {u : X.toCombMap.Dart}
    (ha : X.toCombMap.alpha u ∈ K.secondArc.darts) (hb : X.toCombMap.sigma u ∈ K.secondArc.darts) :
    ∃ h : X.toCombMap.alpha (X.toCombMap.sigma u) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = u := by
  have hcarrier : (cellDarts X j).next (X.toCombMap.alpha u)
      (K.secondArc.mem_cycle_of_mem_darts ha) = X.toCombMap.sigma u :=
    (OuterPinchCornerFix.next_faceBoundary_darts (X.faceBoundary (Embedded.cell X j).face)
      (K.secondArc.mem_cycle_of_mem_darts ha)).trans (OuterPinchCornerFix.facePerm_alpha u)
  have hinf := OuterPinchCornerFix.infix_of_next_of_mem K.secondArc
    (X.faceBoundary (Embedded.cell X j).face).nodup hprop ha hb hcarrier
  have hinf2 := (List.IsInfix.map X.toCombMap.alpha hinf.reverse).trans (invDarts_secondArc_infix K)
  have e : [X.toCombMap.alpha u, X.toCombMap.sigma u].reverse.map X.toCombMap.alpha =
      [X.toCombMap.alpha (X.toCombMap.sigma u), u] := by
    simp [X.toCombMap.alpha_involutive u]
  rw [e] at hinf2
  exact ⟨hinf2.mem (by simp), OuterPinchCornerFix.next_eq_of_infix K.boundary.cycle_nodup hinf2 _⟩

/-- **A corner dart on neither arc.** -/
theorem exists_corner_dart (K : CellPocketFaceSet D eps X i j) (hij : i ≠ j)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length) {z : X.toCombMap.Dart}
    (hone : ¬ ∃ h : X.toCombMap.alpha (X.toCombMap.sigma z) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = z) :
    ∃ wd, (wd = X.toCombMap.alpha z ∨ wd = X.toCombMap.sigma z) ∧ wd ∉ K.firstArc.darts ∧
      wd ∉ K.secondArc.darts := by
  by_cases h1 : X.toCombMap.sigma z ∈ K.firstArc.darts
  · refine ⟨X.toCombMap.alpha z, Or.inl rfl, fun ha => hone (cycle_next_of_firstArc K hfirst ha h1),
      fun ha => hij (Embedded.cell_face_injective X ?_)⟩
    exact (faceOf_mem_arc K.firstArc h1).symm.trans
      ((faceOf_sigma_eq_alpha _ z).trans (faceOf_mem_arc K.secondArc ha))
  · by_cases h2 : X.toCombMap.sigma z ∈ K.secondArc.darts
    · refine ⟨X.toCombMap.alpha z, Or.inl rfl, fun ha => hij (Embedded.cell_face_injective X ?_),
        fun ha => hone (cycle_next_of_secondArc K hsecond ha h2)⟩
      exact (faceOf_mem_arc K.firstArc ha).symm.trans
        ((faceOf_sigma_eq_alpha _ z).symm.trans (faceOf_mem_arc K.secondArc h2))
    · exact ⟨X.toCombMap.sigma z, Or.inr rfl, h1, h2⟩

end Arcs

section Hone

/-- (H2) at the first corner. -/
theorem hone_start {M : CombMap.{v}} {c : List M.Dart} (hnodup : c.Nodup) {d₀ e₀ : M.Dart}
    (hd₀ : d₀ ∈ c) (hnext₀ : c.next d₀ hd₀ = e₀) (hne : M.sigma e₀ ≠ M.alpha d₀) :
    ¬ ∃ h : M.alpha (M.sigma e₀) ∈ c, c.next _ h = e₀ :=
  fun h => hne (OuterPinchCornerFix.sigma_eq_of_cycle_next_e₀ hnodup hd₀ hnext₀ h)

/-- (H2) at the second corner, after the first refinement. -/
theorem hone_second {M M' : CombMap.{v}} (R : RotationRefinement M M') {c : List M.Dart}
    {c' : List M'.Dart} (hc' : c' = c.map R.map) (hnodup : c.Nodup) {d₀ e₀ : M.Dart}
    (hd₀ : d₀ ∈ c) (hnext₀ : c.next d₀ hd₀ = e₀) (hne : M.sigma e₀ ≠ M.alpha d₀) {p : ℕ}
    (hp : 0 < p) (hpz : (M'.sigma ^ p) (R.map e₀) = R.map (M.sigma e₀))
    (hpmid : ∀ t, 0 < t → t < p → ∀ w, (M'.sigma ^ t) (R.map e₀) ≠ R.map w) :
    ¬ ∃ h : M'.alpha (M'.sigma (M'.sigma.symm (R.map (M.alpha d₀)))) ∈ c',
      c'.next _ h = M'.sigma.symm (R.map (M.alpha d₀)) := by
  rintro ⟨h, hn⟩
  have hs : M'.sigma (M'.sigma.symm (R.map (M.alpha d₀))) = R.map (M.alpha d₀) :=
    Equiv.apply_symm_apply _ _
  have ha : M'.alpha (M'.sigma (M'.sigma.symm (R.map (M.alpha d₀)))) = R.map d₀ := by
    rw [hs, R.alpha_map, M.alpha_involutive]
  have hd' : R.map d₀ ∈ c' := by
    rw [hc']
    exact List.mem_map.mpr ⟨d₀, hd₀, rfl⟩
  have hcongr : ∀ (a b : M'.Dart) (ha : a ∈ c') (hb : b ∈ c'), a = b → c'.next a ha = c'.next b hb := by
    rintro a b ha hb rfl
    rfl
  have hz : M'.sigma.symm (R.map (M.alpha d₀)) = R.map e₀ :=
    hn.symm.trans ((hcongr _ _ h hd' ha).trans
      ((next_map_of_eq R.injective hc' hnodup hd₀ hd').trans (congrArg R.map hnext₀)))
  have h1 : M'.sigma (R.map e₀) = R.map (M.alpha d₀) := (congrArg M'.sigma hz).symm.trans hs
  rcases Nat.lt_or_ge 1 p with h1p | h1p
  · exact hpmid 1 Nat.one_pos h1p (M.alpha d₀) (by rw [pow_one]; exact h1)
  · have hp1 : p = 1 := by omega
    subst hp1
    rw [pow_one, h1] at hpz
    exact hne (R.injective hpz).symm

end Hone

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.next_ne_self_of_two_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.exists_corner_dart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.hone_second
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.one_lt_length_of_mem_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.faceOf_sigma_eq_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.faceOf_alpha_sigma_symm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.isGFaceOf_congr
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.faceOf_mem_arc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.invDarts_firstArc_infix
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.invDarts_secondArc_infix
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.two_le_cycle_length
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.cycle_next_of_firstArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.cycle_next_of_secondArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.hone_start
