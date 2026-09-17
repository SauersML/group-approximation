import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.TouchTwoGon
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94DartMinimal
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P01, empty two-gons: reduction of a corner to a switch

Notation: `M = S.diagram.toCombMap`, `φ = M.facePerm`, `α = M.alpha`, and for a dart `d` put
`A t = faceOf (α (φ^t d))`, the face across the `t`-th dart of the boundary walk from `d`.

`TouchCornerStatement` (the residual of `TouchTwoGon`) asks to exclude `CornerExcluded P`.
This module reduces it to the narrower `SwitchCornerStatement`, which asks to exclude
`SwitchCornerExcluded P`: the same configuration, except that every interior dart of the stretch
has the polygon face `P.face k` on both sides (a bridge of `k`).

## Proof of the reduction (formalized here)

Fix `k ≠ k'`, `o ≠ o'`, a dart `d` of `P.face k` with `A 0 = objectFace o` and
`A m = objectFace o'` (`0 < m`).  For `0 < t < m`, `A t` lies in no selected region, and if `A t`
is an object face `objectFace p` then `p ∈ {o, o'}`.  The polygon `k'` touches both `o` and `o'`.

1. *An interior dart across no object is a bridge* (`across_eq_face`).  Let `e = φ^t d`, so
   `faceOf e = P.face k` (`faceOf_pow_switch`).  Suppose `A t` is no object face and lies in no
   selected region.  Then:
   * `faceOf e = P.face k` is not the outer face (`face_ne_outer`), not a relator cell face
     (`face_not_cell`), and in no selected region (`face_unselected`);
   * `A t ≠ objectFace none = outerFace`, and `A t ≠ objectFace (some j) = (cell j).face`;
   * `A t` is in no selected region.
   So `S.DartMinimal.unselectedGFacesMerged` applies at `e` and gives
   `faceOf e = faceOf (α e)`, that is, `A t = P.face k`.
2. *Choose a switch* (`exists_switch`).  Let `j` be the least `j > 0` with
   `A j = objectFace o'` (`Nat.find`, witness `m`), so `j ≤ m`.  Let `i` be the greatest `i ≤ j - 1`
   with `A i = objectFace o` (`Nat.findGreatest`, witness `0`), so `i < j`.  For `i < t < j`:
   * `0 < t < m`;
   * `A t ≠ objectFace o` by maximality of `i`, and `A t ≠ objectFace o'` by minimality of `j`;
   * so, by the hypothesis on interior darts, `A t` is no object face at all.
   Step 1 gives `A t = P.face k`.
3. *Restart at the switch* (`cornerExcluded_of_switch`).  Put `d' = φ^i d` and `m' = j - i > 0`.
   * `faceOf d' = P.face k`.
   * `faceOf (α d') = objectFace o`.
   * `faceOf (α (φ^m' d')) = A j = objectFace o'`, since `φ^m' (φ^i d) = φ^(m'+i) d`.
   * For `0 < s < m'`, `faceOf (α (φ^s d')) = A (s + i) = P.face k`.
   The witnesses for `k'` are unchanged.  So `SwitchCornerExcluded P` gives `False`.

With `touchCorner_of_switch` and `proof_of_corner` this yields `proof_of_switch`:
`SwitchCornerStatement → OsinLemma94ContactMapEmptyTwoGonInput`.

## The residual (open): `SwitchCornerStatement`

It is true, being a special case of `TouchCornerStatement`: a bridge face `P.face k` is unselected
(`face_unselected`) and is not an object face (`objectFace_ne_face`).  Sketch:
* *Bridges.*  The interior darts `φ^s d'` (`0 < s < m'`) have `P.face k` on both sides.  They
  are bridges of the planar map `M`.  The boundary walk of `k'` joins the `o`-boundary to the
  `o'`-boundary while avoiding them, so the bridge path is closed off.  A closed bridge path has a
  leaf `φ c = α c` (`SameFaceForest.exists_leaf`, `BridgeComponent.near1_not_side`), which
  `S.DartMinimal` excludes (`not_leaf_of_dartMinimal`, `pendantPathRemovalInput`).  So `m' = 1`.
* *The triangle.*  At the corner `d', φ d'` carve a triangle across `k`
  (`GFaceWordInsertion.exists_split_corner_output`, transported by `insertionTransport`).  It is a
  singleton contiguity region along `o` and `o'` (`ContiguityGeometry.ofSingletonFace`), avoided by
  every selected region.  This contradicts the weight maximality of `S`
  (`false_of_avoided_singleton`), with the loop and cancellation edge cases handled as in the
  bubble lemmas.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon

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

/-- **The switch exclusion** (open residual): under the binders of `TouchCornerStatement`, a
maximal realized polygon family has no switch configuration `SwitchCornerExcluded`. -/
def SwitchCornerStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal → SwitchCornerExcluded P

/-- **The corner exclusion from the switch exclusion.** -/
theorem touchCorner_of_switch (hswitch : SwitchCornerStatement.{u, w, v}) :
    TouchCornerStatement.{u, w, v} := by
  intro _ _ _ D hhyper lambda c mu h1 h2 h3 h4 h5
  obtain ⟨e0, he0⟩ := hswitch D hhyper lambda c mu h1 h2 h3 h4 h5
  refine ⟨e0, fun eps heps => ?_⟩
  obtain ⟨r0, hr0, hK⟩ := he0 eps heps
  exact ⟨r0, hr0, fun rho hrho W hW Delta cuts hleast hcells hbelow S hcard hminimal P hmax =>
    cornerExcluded_of_switch P hminimal
      (hK rho hrho W hW Delta cuts hleast hcells hbelow S hcard hminimal P hmax)⟩

/-- **The empty two-gon count from the switch exclusion** (reduction; the residual is open). -/
theorem proof_of_switch (hswitch : SwitchCornerStatement.{u, w, v}) :
    OsinLemma94ContactMapEmptyTwoGonInput.{u, w, v} :=
  proof_of_corner (touchCorner_of_switch hswitch)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.across_eq_face
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.exists_switch
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.cornerExcluded_of_switch
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.touchCorner_of_switch
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.proof_of_switch
