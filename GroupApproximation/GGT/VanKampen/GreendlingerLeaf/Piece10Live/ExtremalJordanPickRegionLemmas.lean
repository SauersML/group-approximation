import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# Linked darts: face classes, arcs, and a class free of both arcs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-35.

These are the lemmas behind `extremalJordanPickRegion_region_of_three`.

* A face-class relation is a linking relation (`extremalJordanPickRegion_linked_of_class`).
* Two darts on one face are face-class related (`extremalJordanPickRegion_eqvGen_of_face`).
* A list whose consecutive entries are related has all its entries related
  (`extremalJordanPickRegion_eqvGen_of_chain`).  So the darts of each arc are pairwise linked.
* Among three pairwise unlinked darts, one meets neither arc
  (`extremalJordanPickRegion_free_of_three`), because two darts meeting the same arc are linked.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **Consecutive relations along a list relate all its entries.** -/
theorem extremalJordanPickRegion_eqvGen_of_chain {α : Type*} {R : α → α → Prop} (L : List α)
    (h : ∀ (l₁ l₂ : List α) (x y : α), L = l₁ ++ x :: y :: l₂ → Relation.EqvGen R x y) :
    ∀ x ∈ L, ∀ y ∈ L, Relation.EqvGen R x y := by
  induction L with
  | nil =>
      intro x hx
      simp at hx
  | cons a t ih =>
      have ih' := ih fun l₁ l₂ x y e => h (a :: l₁) l₂ x y (by rw [e, List.cons_append])
      have ha : ∀ z ∈ t, Relation.EqvGen R a z := by
        intro z hz
        cases t with
        | nil => simp at hz
        | cons b t' =>
            exact Relation.EqvGen.trans _ _ _ (h [] t' a b rfl)
              (ih' b (List.mem_cons.mpr (Or.inl rfl)) z hz)
      intro x hx y hy
      rcases List.mem_cons.mp hx with hx | hx <;> rcases List.mem_cons.mp hy with hy | hy
      · rw [hx, hy]
        exact Relation.EqvGen.refl _
      · rw [hx]
        exact ha y hy
      · rw [hy]
        exact Relation.EqvGen.symm _ _ (ha x hx)
      · exact ih' x hx y hy

section PickRegionLemmas

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A face class is linked.** -/
theorem extremalJordanPickRegion_linked_of_class (K : PocketFaceSet D eps X lo hi)
    {x y : X.toCombMap.Dart}
    (h : Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) x y) :
    ExtremalJordanPickRegionLinked K x y := by
  unfold ExtremalJordanPickRegionLinked
  induction h with
  | rel a b hab => exact Relation.EqvGen.rel _ _ (Or.inl hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- **Powers of the face permutation stay in the face class.** -/
theorem extremalJordanPickRegion_eqvGen_pow (K : PocketFaceSet D eps X lo hi)
    (x : X.toCombMap.Dart) (n : ℕ) :
    Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
      x ((X.toCombMap.facePerm ^ n) x) := by
  induction n with
  | zero =>
      rw [pow_zero, Equiv.Perm.one_apply]
      exact Relation.EqvGen.refl _
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ (Or.inl rfl))

/-- **Two darts on one face are in one face class.** -/
theorem extremalJordanPickRegion_eqvGen_of_face (K : PocketFaceSet D eps X lo hi)
    {x y : X.toCombMap.Dart} (h : X.toCombMap.faceOf x = X.toCombMap.faceOf y) :
    Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
      x y := by
  obtain ⟨n, hn⟩ := ((X.toCombMap.faceOf_eq_iff x y).mp h).exists_nat_pow_eq
  rw [← hn]
  exact extremalJordanPickRegion_eqvGen_pow K x n

/-- **The darts of the target arc are pairwise linked.** -/
theorem extremalJordanPickRegion_linked_of_target (K : PocketFaceSet D eps X lo hi)
    {x y : X.toCombMap.Dart} (hx : x ∈ K.targetArc.darts) (hy : y ∈ K.targetArc.darts) :
    ExtremalJordanPickRegionLinked K x y :=
  extremalJordanPickRegion_eqvGen_of_chain (R := ExtremalJordanPickRegionStep K)
    K.targetArc.darts
    (fun l₁ l₂ a b e => Relation.EqvGen.rel _ _ (Or.inr (Or.inr (Or.inl ⟨l₁, l₂, e⟩))))
    x hx y hy

/-- **The darts of the reversed source arc are pairwise linked.** -/
theorem extremalJordanPickRegion_linked_of_invSource (K : PocketFaceSet D eps X lo hi)
    {x y : X.toCombMap.Dart} (hx : x ∈ invDarts X K.sourceArc.darts)
    (hy : y ∈ invDarts X K.sourceArc.darts) :
    ExtremalJordanPickRegionLinked K x y :=
  extremalJordanPickRegion_eqvGen_of_chain (R := ExtremalJordanPickRegionStep K)
    (invDarts X K.sourceArc.darts)
    (fun l₁ l₂ a b e => Relation.EqvGen.rel _ _ (Or.inr (Or.inr (Or.inr ⟨l₁, l₂, e⟩))))
    x hx y hy

/-- **Two classes meeting one arc are linked.**  The arc is the target arc or the reversed
source arc. -/
theorem extremalJordanPickRegion_linked_of_meets (K : PocketFaceSet D eps X lo hi)
    {l : List X.toCombMap.Dart}
    (hl : l = K.targetArc.darts ∨ l = invDarts X K.sourceArc.darts) {a b : X.toCombMap.Dart}
    (ha : ExtremalJordanPickRegionMeets K a l) (hb : ExtremalJordanPickRegionMeets K b l) :
    ExtremalJordanPickRegionLinked K a b := by
  obtain ⟨d, hd, had⟩ := ha
  obtain ⟨d', hd', hbd⟩ := hb
  have hdd : ExtremalJordanPickRegionLinked K d d' := by
    rcases hl with rfl | rfl
    · exact extremalJordanPickRegion_linked_of_target K hd hd'
    · exact extremalJordanPickRegion_linked_of_invSource K hd hd'
  exact Relation.EqvGen.trans _ _ _ (extremalJordanPickRegion_linked_of_class K had)
    (Relation.EqvGen.trans _ _ _ hdd
      (Relation.EqvGen.symm _ _ (extremalJordanPickRegion_linked_of_class K hbd)))

end PickRegionLemmas

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRegion_eqvGen_of_chain
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRegion_linked_of_class
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRegion_eqvGen_pow
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRegion_eqvGen_of_face
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRegion_linked_of_target
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRegion_linked_of_invSource
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRegion_linked_of_meets
