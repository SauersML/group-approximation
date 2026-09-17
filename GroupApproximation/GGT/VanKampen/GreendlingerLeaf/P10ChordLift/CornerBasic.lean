import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.GoodSector
import GroupApproximation.Meta.AxiomGuard

/-!
# Chord lift: the corner digon of a pocket (vocabulary, corner darts, the inner monogon)

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Let `K` be a pocket of `X` with boundary cycle
`c` (no duplicates) in walk order.  For a dart `z` write `f = face (α z) = face (σ z)`
(`faceOf_sigma_eq_alpha`).

## The corner digon (`CornerDigon K z`)

A rotation refinement `R : X → X'` carrying the pocket (`K'` with `c' = c.map R`, the same invariants
and repeated visits) in which the rotation step `z ↦ σ z` lifts to `R z ↦ R (σ z)` in `p` steps, all
intermediate darts new, and for some `m < p` the corner face `g = face' (α' (σ'^m (R z)))` is a G-face
of `X'` (off the exterior, off the relator cells), whose old darts are among `α z`, `σ z`; and every
G-face of `X` other than `f` stays a G-face.

## The hypothesis at a corner

(H2) `α (σ z)` is not followed by `z` in `c`.  It holds at the first corner `z = e₀` of an uncrossed
non-first turn `d₀ → e₀` (`hone_start`, since otherwise `σ e₀ = α d₀`, which is a first turn), and at
the second corner `z₂ = σ₁⁻¹ (R₁ (α d₀))` after the first refinement (`hone_second`: otherwise
`z₂ = R₁ e₀`, so `σ₁ (R₁ e₀) = R₁ (α d₀)` is old, which forces `p₁ = 1` and `σ e₀ = α d₀`).

## Corner darts (`exists_corner_dart_inner`, `exists_corner_dart_outer`)

If `σ z` lies on the (proper) source arc, then `α z` does not: both would be consecutive on the arc, so
`α (σ z)` precedes `z` in `c` (`PocketFaceSet.cycle_next_of_sourceArc`), against (H2).  Symmetrically
on the reversed outer traversal: if `α (σ z)` lies on the target arc then `α (α z) = z` does not
(`PocketFaceSet.cycle_next_of_targetArc`).

## The inner monogon (`cornerDigon_innerMonogon`)

If `σ z = α z` and `f ≠ outer`, then `f` has a single dart (`not_one_lt_length_of_monogon`: on a
duplicate-free traversal of length at least two no dart is its own successor, while the successor of
`α z` is `facePerm (α z) = σ z = α z`).  Relator words have length at least two (`hW`), so `f` is no
relator cell (`one_lt_cell_length`): it is already a G-face.  Take `R = refl`, `p = 1`, `m = 0`; an old
dart `w` on `f` equals `α z` (else `f` has two darts).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift

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

/-- The two darts of a corner lie on one face. -/
theorem faceOf_sigma_eq_alpha (M : CombMap.{v}) (z : M.Dart) :
    M.faceOf (M.sigma z) = M.faceOf (M.alpha z) := by
  have h := M.faceOf_facePerm (M.alpha z)
  rwa [OuterPinchCornerFix.facePerm_alpha] at h

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lo hi : ℕ}

/-- A G-face: off the exterior and off the relator cells. -/
abbrev IsGFaceOf (X : DiscDiagram.{u, w, v} W) (g : X.toCombMap.Face) : Prop :=
  g ≠ X.outerFace ∧ ∀ C ∈ X.relatorCells, C.face ≠ g

theorem isGFaceOf_congr {X : DiscDiagram.{u, w, v} W} {g g' : X.toCombMap.Face} (h : g = g')
    (hg : IsGFaceOf X g') : IsGFaceOf X g :=
  h ▸ hg

/-- The invariants of a pocket carried by the step. -/
abbrev PocketInvariants {X : DiscDiagram.{u, w, v} W} (K : PocketFaceSet D eps X lo hi) : Prop :=
  (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) ∧ K.ClosedWalk ∧
    K.sourceArc.length < (cellDarts X K.source).length ∧
    K.targetArc.length < (outerDarts X).length

/-- **A G-digon in the corner between `z` and `σ z`**, through a refinement carrying the pocket. -/
abbrev CornerDigon {X : DiscDiagram.{u, w, v} W} (K : PocketFaceSet D eps X lo hi)
    (z : X.toCombMap.Dart) : Prop :=
  ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi)
    (R : RotationRefinement X.toCombMap X'.toCombMap),
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

section Arcs

variable {X : DiscDiagram.{u, w, v} W}

/-- **A corner dart off the source arc.** -/
theorem exists_corner_dart_inner (K : PocketFaceSet D eps X lo hi)
    (hprop : K.sourceArc.length < (cellDarts X K.source).length) {z : X.toCombMap.Dart}
    (hone : ¬ ∃ h : X.toCombMap.alpha (X.toCombMap.sigma z) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = z) :
    ∃ wd, (wd = X.toCombMap.alpha z ∨ wd = X.toCombMap.sigma z) ∧ wd ∉ K.sourceArc.darts := by
  by_cases h1 : X.toCombMap.sigma z ∈ K.sourceArc.darts
  · exact ⟨X.toCombMap.alpha z, Or.inl rfl, fun ha => hone (K.cycle_next_of_sourceArc hprop ha h1)⟩
  · exact ⟨X.toCombMap.sigma z, Or.inr rfl, h1⟩

/-- **A corner dart whose reversal is off the target arc.** -/
theorem exists_corner_dart_outer (K : PocketFaceSet D eps X lo hi)
    (htgt : K.targetArc.length < (outerDarts X).length) {z : X.toCombMap.Dart}
    (hone : ¬ ∃ h : X.toCombMap.alpha (X.toCombMap.sigma z) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = z) :
    ∃ wd, (wd = X.toCombMap.alpha z ∨ wd = X.toCombMap.sigma z) ∧
      X.toCombMap.alpha wd ∉ K.targetArc.darts := by
  by_cases h1 : X.toCombMap.alpha (X.toCombMap.sigma z) ∈ K.targetArc.darts
  · refine ⟨X.toCombMap.alpha z, Or.inl rfl, fun ha => hone (K.cycle_next_of_targetArc htgt ?_ h1)⟩
    rwa [X.toCombMap.alpha_involutive] at ha
  · exact ⟨X.toCombMap.sigma z, Or.inr rfl, h1⟩

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
  have hcongr : ∀ (a b : M'.Dart) (ha : a ∈ c') (hb : b ∈ c'), a = b →
      c'.next a ha = c'.next b hb := by
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

section Monogon

variable {X : DiscDiagram.{u, w, v} W}

/-- A monogon corner face has a single dart. -/
theorem not_one_lt_length_of_monogon {g : X.toCombMap.Face} {z : X.toCombMap.Dart}
    (hg : X.toCombMap.faceOf (X.toCombMap.alpha z) = g)
    (hmono : X.toCombMap.sigma z = X.toCombMap.alpha z) :
    ¬ 1 < (X.faceBoundary g).darts.length := by
  intro hlt
  have hmem : X.toCombMap.alpha z ∈ (X.faceBoundary g).darts :=
    ((X.faceBoundary g).mem_iff _).mpr hg
  exact next_ne_self_of_two_le (X.faceBoundary g).nodup hlt hmem
    ((OuterPinchCornerFix.next_faceBoundary_darts (X.faceBoundary g) hmem).trans
      ((OuterPinchCornerFix.facePerm_alpha z).trans hmono))

/-- A relator cell has at least two darts when every relator has at least two letters. -/
theorem one_lt_cell_length (hW : ∀ word ∈ W, 1 < word.length)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells) :
    1 < (X.faceBoundary C.face).darts.length := by
  have h := congrArg List.length (X.relatorCell_word C hC)
  rw [List.length_map] at h
  rw [← h]
  exact hW C.word C.word_mem

/-- **The inner monogon corner** is already a G-face. -/
theorem cornerDigon_innerMonogon (hW : ∀ word ∈ W, 1 < word.length)
    (K : PocketFaceSet D eps X lo hi) (z : X.toCombMap.Dart) (hinv : PocketInvariants K)
    (hfo : X.toCombMap.faceOf (X.toCombMap.alpha z) ≠ X.outerFace)
    (hmono : X.toCombMap.sigma z = X.toCombMap.alpha z) : CornerDigon K z := by
  refine ⟨X, K, RotationRefinement.refl X.toCombMap, ⟨OEquivalentDiscDiagram.refl X⟩, hinv, rfl,
    (List.map_id'' (fun _ => rfl) _).symm, 1, 0, Nat.one_pos, ?_,
    fun t ht ht1 => absurd ht1 (by omega), ?_, ?_,
    fun w hG _ => hG⟩
  · show (X.toCombMap.sigma ^ 1) z = X.toCombMap.sigma z
    rw [pow_one]
  · show IsGFaceOf X (X.toCombMap.faceOf (X.toCombMap.alpha ((X.toCombMap.sigma ^ 0) z)))
    rw [pow_zero, Perm.one_apply]
    exact ⟨hfo, fun C hC hCf => not_one_lt_length_of_monogon hCf.symm hmono (one_lt_cell_length hW hC)⟩
  · intro w hw
    change X.toCombMap.faceOf w =
      X.toCombMap.faceOf (X.toCombMap.alpha ((X.toCombMap.sigma ^ 0) z)) at hw
    rw [pow_zero, Perm.one_apply] at hw
    left
    by_contra hne
    have hmemα : X.toCombMap.alpha z ∈
        (X.faceBoundary (X.toCombMap.faceOf (X.toCombMap.alpha z))).darts :=
      ((X.faceBoundary _).mem_iff _).mpr rfl
    have hmemw : w ∈ (X.faceBoundary (X.toCombMap.faceOf (X.toCombMap.alpha z))).darts :=
      ((X.faceBoundary _).mem_iff _).mpr hw
    exact not_one_lt_length_of_monogon rfl hmono (one_lt_length_of_mem_ne hmemα hmemw (Ne.symm hne))

end Monogon

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.next_ne_self_of_two_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.one_lt_length_of_mem_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.faceOf_sigma_eq_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.exists_corner_dart_inner
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.exists_corner_dart_outer
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.hone_start
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.hone_second
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.not_one_lt_length_of_monogon
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.one_lt_cell_length
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.cornerDigon_innerMonogon
