import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.TouchTwoGon
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94DartMinimal
import GroupApproximation.Meta.AxiomGuard

/-!
# GL01: a corner configuration restarts at a switch

*GL01 copy.*  This re-proves the reduction steps of the foreign module
`GreendlingerLeaf.P01EmptyTwoGon.TouchCornerSwitch` (origin/main blob `556301d24`).  That module is
last changed by a commit marked WIP, so it is not imported.  The declarations live in the namespace
`P01EmptyTwoGon.GL01`, so names resolve as in the original.  Only the residual statement and its
reductions are dropped.

Infrastructure for `thm:hull` in non_mf_groups_exist.tex (Hull's small cancellation theorem),
through Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.4 (the count of empty two-gons of the
contact map).  It certifies no printed sentence on its own.

Notation: `M = S.diagram.toCombMap`, `φ = M.facePerm`, `α = M.alpha`, and for a dart `d`,
`A t = faceOf (α (φ^t d))` is the face across the `t`-th dart of the walk from `d`.

`CornerExcluded P` (module `TouchTwoGon`) says there is no corner configuration.
`cornerExcluded_of_switch` derives it from `SwitchCornerExcluded P`, which excludes the same
configuration with every interior dart having the polygon face `P.face k` on both sides.

1. *An interior dart across no object is a bridge* (`across_eq_face`).  The dart `e = φ^t d` lies
   on `P.face k`, an unselected `G`-face.  If `A t` is no object face and lies in no selected
   region, `S.DartMinimal.unselectedGFacesMerged` gives `A t = P.face k`.
2. *Choose a switch* (`exists_switch`).  Let `j` be the least `j > 0` with `A j = objectFace o'`,
   and `i` the greatest `i ≤ j - 1` with `A i = objectFace o`.  For `i < t < j`, `A t` is no object
   face, so it is `P.face k` by step 1.
3. *Restart at the switch* (`cornerExcluded_of_switch`): take `d' = φ^i d` and `m' = j - i`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open scoped Classical

section TouchCornerSwitch

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- Face steps keep the face. -/
theorem faceOf_pow_switch (x : S.diagram.toCombMap.Dart) (n : ℕ) :
    S.diagram.toCombMap.faceOf ((S.diagram.toCombMap.facePerm ^ n) x) =
      S.diagram.toCombMap.faceOf x := by
  induction n with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, S.diagram.toCombMap.faceOf_facePerm, ih]

/-- Composing two face-step powers. -/
theorem pow_apply_pow_switch (x : S.diagram.toCombMap.Dart) (s i : ℕ) :
    (S.diagram.toCombMap.facePerm ^ s) ((S.diagram.toCombMap.facePerm ^ i) x) =
      (S.diagram.toCombMap.facePerm ^ (s + i)) x := by
  rw [pow_add, Equiv.Perm.mul_apply]

/-- A polygon face is not the face of a relator cell. -/
theorem relatorCell_face_ne (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    ∀ C ∈ S.diagram.relatorCells, C.face ≠ P.face k := by
  intro C hC h
  obtain ⟨i, hi⟩ := List.get_of_mem hC
  refine P.face_not_cell k i ?_
  change (S.diagram.relatorCells.get i).face = P.face k
  rw [hi]
  exact h

/-- **Step 1: an interior dart across no object and no selected region is a bridge of `k`.** -/
theorem across_eq_face (P : OsinLemma94RealizedPolygons S) (hS : S.DartMinimal)
    {k : Fin P.count} {e : S.diagram.toCombMap.Dart}
    (he : S.diagram.toCombMap.faceOf e = P.face k)
    (hsel : ∀ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e) ∉ a.1)
    (hobj : ∀ p : Option (Fin S.diagram.rCellCount),
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e) ≠
        OsinLemma94RealizedPolygons.objectFace S p) :
    S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e) = P.face k := by
  refine (hS.unselectedGFacesMerged e ?_ (hobj none) ?_ ?_).symm.trans he
  · rw [he]
    exact P.face_ne_outer k
  · intro C hC
    refine ⟨by rw [he]; exact relatorCell_face_ne P k C hC, fun h => ?_⟩
    obtain ⟨i, hi⟩ := List.get_of_mem hC
    refine hobj (some i) ?_
    change S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e) =
      (S.diagram.relatorCells.get i).face
    rw [hi]
    exact h.symm
  · intro b hb
    exact ⟨by rw [he]; exact P.face_unselected k b hb, hsel b hb⟩

/-- **Step 2: a switch** between the last contact with `o` and the first contact with `o'`, with
only bridges of `k` in between. -/
theorem exists_switch (P : OsinLemma94RealizedPolygons S) (hS : S.DartMinimal)
    {k : Fin P.count} {o o' : Option (Fin S.diagram.rCellCount)}
    {d : S.diagram.toCombMap.Dart} {m : ℕ} (hm : 0 < m)
    (hd : S.diagram.toCombMap.faceOf d = P.face k)
    (h0 : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) =
      OsinLemma94RealizedPolygons.objectFace S o)
    (hmo : S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ m) d)) =
        OsinLemma94RealizedPolygons.objectFace S o')
    (hint : ∀ i : ℕ, 0 < i → i < m →
      (∀ a ∈ S.family, S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ i) d)) ∉ a.1) ∧
      ∀ p : Option (Fin S.diagram.rCellCount), S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ i) d)) =
          OsinLemma94RealizedPolygons.objectFace S p → p = o ∨ p = o') :
    ∃ i j : ℕ, i < j ∧
      S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ i) d)) =
          OsinLemma94RealizedPolygons.objectFace S o ∧
      S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ j) d)) =
          OsinLemma94RealizedPolygons.objectFace S o' ∧
      ∀ t : ℕ, i < t → t < j → S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ t) d)) = P.face k := by
  have hex : ∃ j : ℕ, 0 < j ∧ S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ j) d)) =
        OsinLemma94RealizedPolygons.objectFace S o' := ⟨m, hm, hmo⟩
  obtain ⟨j, ⟨hj0, hjo⟩, hjm, hjmin⟩ : ∃ j : ℕ, (0 < j ∧ S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ j) d)) =
        OsinLemma94RealizedPolygons.objectFace S o') ∧ j ≤ m ∧
      ∀ t : ℕ, 0 < t → t < j → S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ t) d)) ≠
          OsinLemma94RealizedPolygons.objectFace S o' :=
    ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex ⟨hm, hmo⟩,
      fun t ht htj h => Nat.find_min hex htj ⟨ht, h⟩⟩
  obtain ⟨i, hio, hij, himax⟩ : ∃ i : ℕ, S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ i) d)) =
        OsinLemma94RealizedPolygons.objectFace S o ∧ i < j ∧
      ∀ t : ℕ, i < t → t < j → S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ t) d)) ≠
          OsinLemma94RealizedPolygons.objectFace S o := by
    refine ⟨Nat.findGreatest (fun t => S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ t) d)) =
          OsinLemma94RealizedPolygons.objectFace S o) (j - 1),
      Nat.findGreatest_spec (P := fun t => S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ t) d)) =
          OsinLemma94RealizedPolygons.objectFace S o) (Nat.zero_le (j - 1)) ?_,
      (Nat.findGreatest_le (P := fun t => S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ t) d)) =
          OsinLemma94RealizedPolygons.objectFace S o) (j - 1)).trans_lt
        (Nat.sub_lt hj0 Nat.zero_lt_one),
      fun t ht htj => Nat.findGreatest_is_greatest (P := fun t => S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ t) d)) =
          OsinLemma94RealizedPolygons.objectFace S o) ht (by omega)⟩
    show S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ 0) d)) =
        OsinLemma94RealizedPolygons.objectFace S o
    rw [pow_zero, Equiv.Perm.one_apply]
    exact h0
  refine ⟨i, j, hij, hio, hjo, fun t hit htj => ?_⟩
  have htm : t < m := lt_of_lt_of_le htj hjm
  have ht0 : 0 < t := lt_of_le_of_lt (Nat.zero_le i) hit
  refine across_eq_face P hS ((faceOf_pow_switch d t).trans hd) (hint t ht0 htm).1
    (fun p hp => ?_)
  rcases (hint t ht0 htm).2 p hp with h | h
  · rw [h] at hp
    exact himax t hit htj hp
  · rw [h] at hp
    exact hjmin t ht0 htj hp

/-- **The switch configuration**: a polygon `k` whose boundary runs from a dart across `o` to a
dart across `o′ ≠ o` through bridges of `k`, while a second polygon `k′` touches both `o` and
`o′`. -/
def SwitchCornerExcluded (P : OsinLemma94RealizedPolygons S) : Prop :=
  ∀ k k' : Fin P.count, k ≠ k' →
    ∀ o o' : Option (Fin S.diagram.rCellCount), o ≠ o' →
      ∀ (d : S.diagram.toCombMap.Dart) (m : ℕ), 0 < m →
        S.diagram.toCombMap.faceOf d = P.face k →
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) =
          OsinLemma94RealizedPolygons.objectFace S o →
        S.diagram.toCombMap.faceOf
          (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ m) d)) =
          OsinLemma94RealizedPolygons.objectFace S o' →
        (∀ i : ℕ, 0 < i → i < m → S.diagram.toCombMap.faceOf
          (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ i) d)) = P.face k) →
        (∃ e, S.diagram.toCombMap.faceOf e = P.face k' ∧ S.diagram.toCombMap.faceOf
          (S.diagram.toCombMap.alpha e) = OsinLemma94RealizedPolygons.objectFace S o) →
        (∃ e, S.diagram.toCombMap.faceOf e = P.face k' ∧ S.diagram.toCombMap.faceOf
          (S.diagram.toCombMap.alpha e) = OsinLemma94RealizedPolygons.objectFace S o') →
        False

/-- **Step 3: the corner configuration from the switch configuration.** -/
theorem cornerExcluded_of_switch (P : OsinLemma94RealizedPolygons S) (hS : S.DartMinimal)
    (hswitch : SwitchCornerExcluded P) : CornerExcluded P := by
  intro k k' hkk o o' hoo d m hm hd h0 hmo hint hw hw'
  obtain ⟨i, j, hij, hio, hjo, hmid⟩ := exists_switch P hS hm hd h0 hmo hint
  refine hswitch k k' hkk o o' hoo ((S.diagram.toCombMap.facePerm ^ i) d) (j - i)
    (Nat.sub_pos_of_lt hij) ((faceOf_pow_switch d i).trans hd) hio ?_ ?_ hw hw'
  · rw [pow_apply_pow_switch d (j - i) i, Nat.sub_add_cancel hij.le]
    exact hjo
  · intro s hs hsji
    rw [pow_apply_pow_switch d s i]
    exact hmid (s + i) (by omega) (by omega)

end TouchCornerSwitch

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01.across_eq_face
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01.exists_switch
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01.cornerExcluded_of_switch
