import GroupApproximation.Manuscript.NonMF.Full.GL06d.GoodSector
import GroupApproximation.Meta.AxiomGuard

/-!
# Non-rose step: the corner digon of a pocket (vocabulary, corner darts, the inner monogon)

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Let `K` be a pocket of `X` whose boundary
cycle `c` has no duplicates and is listed in walk order.  For a dart `z`, the two corner darts
`α z` and `σ z` lie on one face (`faceOf_sigma_eq_alpha`).

* `CornerDigon K z`: a rotation refinement `R : X → X'` that carries the pocket, in which the step
  `z ↦ σ z` lifts to `p` rotation steps through new darts only, and some intermediate corner face
  is a G-face of `X'` whose old darts are among `α z` and `σ z`.
* `exists_corner_dart_inner` and `exists_corner_dart_outer`: unless `α (σ z)` is followed by `z` in
  `c`, some corner dart avoids the proper source arc, and some reversed corner dart avoids the
  proper target arc.
* `hone_start` and `hone_second`: that hypothesis holds at the two corners of an uncrossed
  non-first turn `d₀ → e₀`.
* `cornerDigon_innerMonogon`: if `σ z = α z` off the exterior, the corner face is a monogon.  Every
  relator has at least two letters, so the monogon is already a G-face.

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`; Hull's small cancellation theorem,
through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL06d

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.OuterPinchIsolated
open GroupApproximation.GGT.VanKampen.OuterPinchCorners
open GroupApproximation.GGT.VanKampen.OuterPinchCornerFix
open scoped Classical

section Lists

variable {β : Type*}

/-- In a duplicate-free list of length at least two, no entry is its own successor
(`thm:hull`). -/
theorem next_ne_self_of_two_le {l : List β} (hl : l.Nodup) (h2 : 2 ≤ l.length) {a : β}
    (ha : a ∈ l) : l.next a ha ≠ a := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  intro heq
  rw [List.next_getElem l hl i hi, hl.getElem_inj_iff] at heq
  by_cases hlt : i + 1 < l.length
  · rw [Nat.mod_eq_of_lt hlt] at heq
    omega
  · have hn : i + 1 = l.length := by omega
    rw [hn, Nat.mod_self] at heq
    omega

/-- A list with two distinct members has length at least two (`thm:hull`). -/
theorem one_lt_length_of_mem_ne {l : List β} {a b : β} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    1 < l.length := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  by_contra hle
  have hij : i = j := by omega
  subst hij
  exact hab rfl

end Lists

/-- The two darts of a corner lie on one face (`thm:hull`). -/
theorem faceOf_sigma_eq_alpha (M : CombMap.{v}) (z : M.Dart) :
    M.faceOf (M.sigma z) = M.faceOf (M.alpha z) :=
  Surgery.PocketGlue.faceOf_sigma_eq M z

/-- On a monogon corner `σ z = α z`, the only dart on the face of `α z` is `α z` itself
(`thm:hull`). -/
theorem eq_alpha_of_monogon {M : CombMap.{v}} {z x : M.Dart} (hmono : M.sigma z = M.alpha z)
    (hx : M.faceOf x = M.faceOf (M.alpha z)) : x = M.alpha z := by
  have hsc : M.facePerm.SameCycle (M.alpha z) x := (M.faceOf_eq_iff _ _).mp hx.symm
  have hfix : Function.IsFixedPt M.facePerm (M.alpha z) := by
    change M.facePerm (M.alpha z) = M.alpha z
    rw [OuterPinchCornerFix.facePerm_alpha, hmono]
  exact (hsc.eq_of_left hfix).symm

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lo hi : ℕ}

/-- A G-face: off the exterior and off the relator cells (`thm:hull`). -/
abbrev IsGFaceOf (X : DiscDiagram.{u, w, v} W) (g : X.toCombMap.Face) : Prop :=
  g ≠ X.outerFace ∧ ∀ C ∈ X.relatorCells, C.face ≠ g

/-- Being a G-face depends only on the face (`thm:hull`). -/
theorem isGFaceOf_congr {X : DiscDiagram.{u, w, v} W} {g g' : X.toCombMap.Face} (h : g = g')
    (hg : IsGFaceOf X g') : IsGFaceOf X g := by
  subst h
  exact hg

/-- The invariants of a pocket that the step carries (`thm:hull`). -/
abbrev PocketInvariants {X : DiscDiagram.{u, w, v} W} (K : PocketFaceSet D eps X lo hi) : Prop :=
  (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) ∧ K.ClosedWalk ∧
    K.sourceArc.length < (cellDarts X K.source).length ∧
    K.targetArc.length < (outerDarts X).length

/-- **A G-digon in the corner between `z` and `σ z`**, through a refinement that carries the pocket
(`thm:hull`). -/
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

/-- **A corner dart off the source arc** (`thm:hull`). -/
theorem exists_corner_dart_inner (K : PocketFaceSet D eps X lo hi)
    (hprop : K.sourceArc.length < (cellDarts X K.source).length) {z : X.toCombMap.Dart}
    (hone : ¬ ∃ h : X.toCombMap.alpha (X.toCombMap.sigma z) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = z) :
    ∃ wd, (wd = X.toCombMap.alpha z ∨ wd = X.toCombMap.sigma z) ∧ wd ∉ K.sourceArc.darts := by
  by_contra hno
  apply hone
  refine K.cycle_next_of_sourceArc hprop ?_ ?_
  · by_contra hz
    exact hno ⟨_, Or.inl rfl, hz⟩
  · by_contra hz
    exact hno ⟨_, Or.inr rfl, hz⟩

/-- **A corner dart whose reversal is off the target arc** (`thm:hull`). -/
theorem exists_corner_dart_outer (K : PocketFaceSet D eps X lo hi)
    (htgt : K.targetArc.length < (outerDarts X).length) {z : X.toCombMap.Dart}
    (hone : ¬ ∃ h : X.toCombMap.alpha (X.toCombMap.sigma z) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = z) :
    ∃ wd, (wd = X.toCombMap.alpha z ∨ wd = X.toCombMap.sigma z) ∧
      X.toCombMap.alpha wd ∉ K.targetArc.darts := by
  by_contra hno
  apply hone
  refine K.cycle_next_of_targetArc htgt ?_ ?_
  · by_contra hz
    refine hno ⟨X.toCombMap.alpha z, Or.inl rfl, ?_⟩
    rwa [X.toCombMap.alpha_involutive]
  · by_contra hz
    exact hno ⟨_, Or.inr rfl, hz⟩

end Arcs

section Hone

/-- The corner hypothesis at the first corner `e₀` (`thm:hull`). -/
theorem hone_start {M : CombMap.{v}} {c : List M.Dart} (hnodup : c.Nodup) {d₀ e₀ : M.Dart}
    (hd₀ : d₀ ∈ c) (hnext₀ : c.next d₀ hd₀ = e₀) (hne : M.sigma e₀ ≠ M.alpha d₀) :
    ¬ ∃ h : M.alpha (M.sigma e₀) ∈ c, c.next _ h = e₀ := by
  intro hex
  exact hne (OuterPinchCornerFix.sigma_eq_of_cycle_next_e₀ hnodup hd₀ hnext₀ hex)

/-- The corner hypothesis at the second corner, after the first refinement (`thm:hull`). -/
theorem hone_second {M M' : CombMap.{v}} (R : RotationRefinement M M') {c : List M.Dart}
    {c' : List M'.Dart} (hc' : c' = c.map R.map) (hnodup : c.Nodup) {d₀ e₀ : M.Dart}
    (hd₀ : d₀ ∈ c) (hnext₀ : c.next d₀ hd₀ = e₀) (hne : M.sigma e₀ ≠ M.alpha d₀) {p : ℕ}
    (hp : 0 < p) (hpz : (M'.sigma ^ p) (R.map e₀) = R.map (M.sigma e₀))
    (hpmid : ∀ t, 0 < t → t < p → ∀ w, (M'.sigma ^ t) (R.map e₀) ≠ R.map w) :
    ¬ ∃ h : M'.alpha (M'.sigma (M'.sigma.symm (R.map (M.alpha d₀)))) ∈ c',
      c'.next _ h = M'.sigma.symm (R.map (M.alpha d₀)) := by
  intro hex
  obtain ⟨h, hn⟩ := hex
  have hsym : M'.alpha (M'.sigma (M'.sigma.symm (R.map (M.alpha d₀)))) = R.map d₀ := by
    rw [Equiv.apply_symm_apply, R.alpha_map, M.alpha_involutive]
  have key : ∀ (x : M'.Dart) (hx : x ∈ c'), x = R.map d₀ → c'.next x hx = R.map e₀ := by
    intro x hx hxe
    subst hxe
    rw [next_map_of_eq R.injective hc' hnodup hd₀ hx, hnext₀]
  have h1 : M'.sigma.symm (R.map (M.alpha d₀)) = R.map e₀ := hn.symm.trans (key _ h hsym)
  have h2 : M'.sigma (R.map e₀) = R.map (M.alpha d₀) := by
    rw [← h1, Equiv.apply_symm_apply]
  by_cases hp1 : p = 1
  · subst hp1
    rw [pow_one, h2] at hpz
    exact hne (R.injective hpz).symm
  · refine hpmid 1 Nat.one_pos (by omega) (M.alpha d₀) ?_
    rw [pow_one]
    exact h2

end Hone

section Monogon

variable {X : DiscDiagram.{u, w, v} W}

/-- A monogon corner face has a single dart (`thm:hull`). -/
theorem not_one_lt_length_of_monogon {g : X.toCombMap.Face} {z : X.toCombMap.Dart}
    (hg : X.toCombMap.faceOf (X.toCombMap.alpha z) = g)
    (hmono : X.toCombMap.sigma z = X.toCombMap.alpha z) :
    ¬ 1 < (X.faceBoundary g).darts.length := by
  intro hlen
  have hlt0 : 0 < (X.faceBoundary g).darts.length := by omega
  have h0 : (X.faceBoundary g).darts[0]'hlt0 = X.toCombMap.alpha z :=
    eq_alpha_of_monogon hmono
      ((((X.faceBoundary g).mem_iff _).mp (List.getElem_mem hlt0)).trans hg.symm)
  have h1 : (X.faceBoundary g).darts[1]'hlen = X.toCombMap.alpha z :=
    eq_alpha_of_monogon hmono
      ((((X.faceBoundary g).mem_iff _).mp (List.getElem_mem hlen)).trans hg.symm)
  have h01 := ((X.faceBoundary g).nodup.getElem_inj_iff).mp (h0.trans h1.symm)
  omega

/-- A relator cell has at least two darts when every relator has at least two letters
(`thm:hull`). -/
theorem one_lt_cell_length (hW : ∀ word ∈ W, 1 < word.length)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells) :
    1 < (X.faceBoundary C.face).darts.length := by
  have hlen := congrArg List.length (X.relatorCell_word C hC)
  rw [List.length_map] at hlen
  rw [← hlen]
  exact hW C.word C.word_mem

/-- **The inner monogon corner** is already a G-face (`thm:hull`). -/
theorem cornerDigon_innerMonogon (hW : ∀ word ∈ W, 1 < word.length)
    (K : PocketFaceSet D eps X lo hi) (z : X.toCombMap.Dart) (hinv : PocketInvariants K)
    (hfo : X.toCombMap.faceOf (X.toCombMap.alpha z) ≠ X.outerFace)
    (hmono : X.toCombMap.sigma z = X.toCombMap.alpha z) : CornerDigon K z := by
  refine ⟨X, K, RotationRefinement.refl X.toCombMap, ⟨OEquivalentDiscDiagram.refl X⟩, hinv, rfl,
    (List.map_id' _).symm, 1, 0, Nat.one_pos, ?_, ?_, ?_, ?_, ?_⟩
  · show (X.toCombMap.sigma ^ 1) z = X.toCombMap.sigma z
    rw [pow_one]
  · intro t ht ht1 _
    omega
  · show IsGFaceOf X (X.toCombMap.faceOf (X.toCombMap.alpha ((X.toCombMap.sigma ^ 0) z)))
    rw [pow_zero, Equiv.Perm.one_apply]
    refine ⟨hfo, fun C hC hCf => ?_⟩
    have hcell := one_lt_cell_length hW hC
    rw [hCf] at hcell
    exact not_one_lt_length_of_monogon rfl hmono hcell
  · intro x hx
    change X.toCombMap.faceOf x =
      X.toCombMap.faceOf (X.toCombMap.alpha ((X.toCombMap.sigma ^ 0) z)) at hx
    rw [pow_zero, Equiv.Perm.one_apply] at hx
    exact Or.inl (eq_alpha_of_monogon hmono hx)
  · intro x hG _
    exact hG

end Monogon

end GroupApproximation.Full.GL06d

#audit_axioms GroupApproximation.Full.GL06d.next_ne_self_of_two_le
#audit_axioms GroupApproximation.Full.GL06d.one_lt_length_of_mem_ne
#audit_axioms GroupApproximation.Full.GL06d.faceOf_sigma_eq_alpha
#audit_axioms GroupApproximation.Full.GL06d.eq_alpha_of_monogon
#audit_axioms GroupApproximation.Full.GL06d.isGFaceOf_congr
#audit_axioms GroupApproximation.Full.GL06d.exists_corner_dart_inner
#audit_axioms GroupApproximation.Full.GL06d.exists_corner_dart_outer
#audit_axioms GroupApproximation.Full.GL06d.hone_start
#audit_axioms GroupApproximation.Full.GL06d.hone_second
#audit_axioms GroupApproximation.Full.GL06d.not_one_lt_length_of_monogon
#audit_axioms GroupApproximation.Full.GL06d.one_lt_cell_length
#audit_axioms GroupApproximation.Full.GL06d.cornerDigon_innerMonogon
