import GroupApproximation.GGT.VanKampen.CombMapRestrictionPlanarity

/-!
# Face classes of a connected planar restriction

Advance around ambient faces and cross ambient edges that are not retained.
In a planar ambient map this equivalence never passes between two different
faces of a connected restriction. The proof grows the restriction one actual
edge at a time. An added edge between different faces joins them in the
smaller map. An added edge on one face must be a spur: otherwise deleting it
from the grown planar map would raise the Euler characteristic above two.

This is the Jordan-type separation used for the Euler count of Osin's graph
`Φ'_M` (Osin, arXiv:math/0411039v3, proof of Lemma 9.7(a)): whatever lies inside
a face of the retained graph stays in that face.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv PermOrbitErasePoint

universe u v

namespace CombMap

/-- An equivalence closure with one extra symmetric pair either avoids the pair
or passes through it once. -/
theorem eqvGen_cases_of_pair {α : Type u} {R S : α → α → Prop} {a b x y : α}
    (hRS : ∀ x₁ x₂, S x₁ x₂ →
      R x₁ x₂ ∨ (x₁ = a ∧ x₂ = b) ∨ (x₁ = b ∧ x₂ = a))
    (h : Relation.EqvGen S x y) :
    Relation.EqvGen R x y ∨ (Relation.EqvGen R x a ∧ Relation.EqvGen R b y) ∨
      (Relation.EqvGen R x b ∧ Relation.EqvGen R a y) := by
  induction h with
  | rel x₁ x₂ hx =>
      rcases hRS x₁ x₂ hx with hr | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (.rel _ _ hr)
      · exact Or.inr (Or.inl ⟨.refl _, .refl _⟩)
      · exact Or.inr (Or.inr ⟨.refl _, .refl _⟩)
  | refl x₁ => exact Or.inl (.refl _)
  | symm x₁ x₂ _ ih =>
      rcases ih with hr | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl hr.symm
      · exact Or.inr (Or.inr ⟨h₂.symm, h₁.symm⟩)
      · exact Or.inr (Or.inl ⟨h₂.symm, h₁.symm⟩)
  | trans x₁ x₂ x₃ _ _ ih₁ ih₂ =>
      rcases ih₁ with h₁ | ⟨h₁, h₁'⟩ | ⟨h₁, h₁'⟩ <;>
        rcases ih₂ with h₂ | ⟨h₂, h₂'⟩ | ⟨h₂, h₂'⟩
      · exact Or.inl (Relation.EqvGen.trans _ _ _ h₁ h₂)
      · exact Or.inr (Or.inl ⟨Relation.EqvGen.trans _ _ _ h₁ h₂, h₂'⟩)
      · exact Or.inr (Or.inr ⟨Relation.EqvGen.trans _ _ _ h₁ h₂, h₂'⟩)
      · exact Or.inr (Or.inl ⟨h₁, Relation.EqvGen.trans _ _ _ h₁' h₂⟩)
      · exact Or.inr (Or.inl ⟨h₁, h₂'⟩)
      · exact Or.inl (Relation.EqvGen.trans _ _ _ h₁ h₂')
      · exact Or.inr (Or.inr ⟨h₁, Relation.EqvGen.trans _ _ _ h₁' h₂⟩)
      · exact Or.inl (Relation.EqvGen.trans _ _ _ h₁ h₂')
      · exact Or.inr (Or.inr ⟨h₁, h₂'⟩)

/-- One elementary move inside a face class of a retained dart set: advance
around an ambient face, or cross an ambient edge that is not retained. -/
def FaceClassStep (M : CombMap.{u}) (keep : M.Dart → Prop) (x y : M.Dart) : Prop :=
  y = M.facePerm x ∨ (¬ keep x ∧ y = M.alpha x)

/-- When every dart is retained, a face class is an ambient face cycle. -/
theorem facePerm_sameCycle_of_faceClass (M : CombMap.{u}) {keep : M.Dart → Prop}
    {x y : M.Dart} (hp : Relation.EqvGen (FaceClassStep M keep) x y)
    (hkeep : ∀ z, keep z) : M.facePerm.SameCycle x y := by
  induction hp with
  | rel x₁ x₂ hx =>
      rcases hx with rfl | ⟨hnot, _⟩
      · exact ⟨1, by rw [zpow_one]⟩
      · exact (hnot (hkeep x₁)).elim
  | refl x₁ => exact Equiv.Perm.SameCycle.refl _ _
  | symm x₁ x₂ _ ih => exact ih.symm
  | trans x₁ x₂ x₃ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

namespace IsRestriction

variable {M : CombMap.{u}} {N : CombMap.{v}} {e : N.Dart ↪ M.Dart}

/-- Retaining every dart makes face rotation the ambient face rotation. -/
theorem facePerm_firstReturn_of_surjective (h : M.IsRestriction N e)
    (he : Function.Surjective e) :
    PermFirstReturn.IsFirstReturn M.facePerm N.facePerm e := by
  intro d
  refine ⟨1, by omega, ?_, by intro k hk hk1; omega⟩
  have hs := PermFirstReturn.apply_eq_of_mem_range _ _ _ h.sigma_firstReturn
    (N.alpha d) (he _)
  rw [pow_one]
  change M.sigma (M.alpha (e d)) = e (N.sigma (N.alpha d))
  rw [← h.alpha_map]
  exact hs

theorem facePerm_sameCycle_iff_of_surjective (h : M.IsRestriction N e)
    (he : Function.Surjective e) (d d' : N.Dart) :
    N.facePerm.SameCycle d d' ↔ M.facePerm.SameCycle (e d) (e d') :=
  PermFirstReturn.sameCycle_iff _ _ _ (h.facePerm_firstReturn_of_surjective he) d d'

/-- A restriction retaining every dart transports connectedness upwards. -/
theorem connected_of_surjective (h : M.IsRestriction N e) (he : Function.Surjective e)
    (hN : N.IsConnected) : M.IsConnected := by
  intro x y
  obtain ⟨d, rfl⟩ := he x
  obtain ⟨d', rfl⟩ := he y
  exact h.reachable (hN d d')

end IsRestriction

end CombMap

namespace EdgeDeletion

variable (M : CombMap.{u}) [DecidableEq M.Dart] (a : M.Dart)

/-- When the reverse dart is alone at its vertex, the joined face rotation
skips that reverse dart in its old face cycle. -/
theorem joinedFacePerm_eq_isolate (hb : M.sigma (M.alpha a) = M.alpha a) :
    joinedFacePerm M a = isolate M.facePerm (M.alpha a) := by
  have hfa : M.facePerm a = M.alpha a := hb
  refine Equiv.ext fun x => ?_
  rw [joinedFacePerm_eq]
  simp only [isolate, Perm.mul_apply]
  by_cases hx : x = a
  · rw [hx]
    simp only [Equiv.swap_apply_left, hfa]
  · by_cases hx' : x = M.alpha a
    · rw [hx']
      simp only [Equiv.swap_apply_right, hfa]
    · have h₁ : M.facePerm x ≠ M.alpha a :=
        fun hq => hx (M.facePerm.injective (hq.trans hfa.symm))
      have h₂ : M.facePerm x ≠ M.facePerm (M.alpha a) :=
        fun hq => hx' (M.facePerm.injective hq)
      rw [Equiv.swap_apply_of_ne_of_ne hx hx', Equiv.swap_apply_of_ne_of_ne h₁ h₂]

/-- Deleting a spur keeps every other old face identification. -/
theorem joinedFacePerm_sameCycle_of_spur (hb : M.sigma (M.alpha a) = M.alpha a)
    {x y : M.Dart} (hx : x ≠ M.alpha a) (hy : y ≠ M.alpha a)
    (hxy : M.facePerm.SameCycle x y) : (joinedFacePerm M a).SameCycle x y := by
  rw [joinedFacePerm_eq_isolate M a hb]
  have hret : ((isolate M.facePerm (M.alpha a)).subtypePerm
      (isolate_ne_iff M.facePerm (M.alpha a))).SameCycle ⟨x, hx⟩ ⟨y, hy⟩ :=
    (PermFirstReturn.sameCycle_iff _ _ _
      (PermOrbitErasePoint.firstReturn M.facePerm (M.alpha a)) ⟨x, hx⟩ ⟨y, hy⟩).mpr hxy
  exact Equiv.Perm.sameCycle_subtypePerm.mp hret

/-- In a planar map, an edge with both endpoints of degree at least two whose
deletion leaves a connected map separates two different faces. Otherwise the
deletion would have Euler characteristic four. -/
theorem faceOf_ne_of_planar (hM : M.IsPlanar) (d : Dart M a)
    (hc : (toCombMap M a).IsConnected) (ha : M.sigma a ≠ a)
    (hb : M.sigma (M.alpha a) ≠ M.alpha a) : M.faceOf a ≠ M.faceOf (M.alpha a) := by
  intro hface
  have hbal := euler_balance_of_sameFace M a hface
  have hv := vertexCount_eq_of_sigma_ne M a hM.1 d ha hb
  have hle := CombMap.eulerCharacteristic_le_two (toCombMap M a) hc
  rw [hv, hM.2] at hbal
  omega

/-- Old face identifications away from the reverse dart survive in the joined
rotation of a planar map, when the deleted edge leaves a connected map and its
first dart is not alone at its vertex. -/
theorem joinedFacePerm_sameCycle_of_planar (hM : M.IsPlanar) (d : Dart M a)
    (hc : (toCombMap M a).IsConnected) (ha : M.sigma a ≠ a) {x y : M.Dart}
    (hx : x ≠ M.alpha a) (hy : y ≠ M.alpha a) (hxy : M.facePerm.SameCycle x y) :
    (joinedFacePerm M a).SameCycle x y := by
  by_cases hb : M.sigma (M.alpha a) = M.alpha a
  · exact joinedFacePerm_sameCycle_of_spur M a hb hx hy hxy
  · exact joinedFacePerm_of_sameCycle M a (faceOf_ne_of_planar M a hM d hc ha hb) hxy

end EdgeDeletion

namespace CombMap.RestrictionGrowth

variable {M : CombMap.{u}} {N : CombMap.{v}} {e : N.Dart ↪ M.Dart}
  (h : M.IsRestriction N e) (a : M.Dart) [DecidableEq M.Dart]

local instance faceClassDecidableEq : DecidableEq (toCombMap h a).Dart :=
  inferInstanceAs (DecidableEq {x : M.Dart // keep (e := e) a x})

/-- One growth step: face classes of the grown core separate its faces, hence
face classes of the old core separate the old faces. -/
theorem faceOf_eq_of_grown (hM : M.IsPlanar) (hN : N.IsConnected) (ha : a ∉ Set.range e)
    (b : N.Dart) (hv : M.vertexOf a = M.vertexOf (e b))
    (ih : ∀ x y : (toCombMap h a).Dart,
      Relation.EqvGen (FaceClassStep M (· ∈ Set.range (ambientEmbedding h a)))
          (ambientEmbedding h a x) (ambientEmbedding h a y) →
        (toCombMap h a).faceOf x = (toCombMap h a).faceOf y)
    {d d' : N.Dart} (hp : Relation.EqvGen (FaceClassStep M (· ∈ Set.range e)) (e d) (e d')) :
    N.faceOf d = N.faceOf d' := by
  have hL : M.IsRestriction (toCombMap h a) (ambientEmbedding h a) := ambientRestriction h a
  have hLc : (toCombMap h a).IsConnected := connected h a hN b hv
  have hLp : (toCombMap h a).IsPlanar := hL.planar hM hLc (newDart h a)
  have hdc : (EdgeDeletion.toCombMap (toCombMap h a) (newDart h a)).IsConnected :=
    (deleted_isRestriction h a ha).connected_of_surjective
      (deletedEmbedding_surjective h a ha) hN
  have hn : (toCombMap h a).sigma (newDart h a) ≠ newDart h a := by
    intro hfix
    obtain ⟨i, hi⟩ := ((toCombMap h a).vertexOf_eq_iff _ _).mp
      ((hL.vertexOf_eq_iff (newDart h a) (oldEmbedding h a b)).mpr hv)
    exact old_ne_new h a ha b
      (hi.symm.trans (Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfix i))
  have hjoin : ∀ {x y : (toCombMap h a).Dart}, x ≠ (toCombMap h a).alpha (newDart h a) →
      y ≠ (toCombMap h a).alpha (newDart h a) → (toCombMap h a).facePerm.SameCycle x y →
        (EdgeDeletion.joinedFacePerm (toCombMap h a) (newDart h a)).SameCycle x y :=
    fun hx hy hxy => EdgeDeletion.joinedFacePerm_sameCycle_of_planar (toCombMap h a)
      (newDart h a) hLp (deletedEmbedding h a ha b) hdc hn hx hy hxy
  have hsc : ∀ x y : (toCombMap h a).Dart,
      Relation.EqvGen (FaceClassStep M (· ∈ Set.range (ambientEmbedding h a)))
          (ambientEmbedding h a x) (ambientEmbedding h a y) →
        (toCombMap h a).facePerm.SameCycle x y :=
    fun x y hxy => ((toCombMap h a).faceOf_eq_iff x y).mp (ih x y hxy)
  have hd := old_ne_reverse h a ha d
  have hd' := old_ne_reverse h a ha d'
  rw [N.faceOf_eq_iff, (deleted_isRestriction h a ha).facePerm_sameCycle_iff_of_surjective
    (deletedEmbedding_surjective h a ha)]
  refine (EdgeDeletion.faceSameCycle_iff (toCombMap h a) (newDart h a) _ _).mpr ?_
  change (EdgeDeletion.joinedFacePerm (toCombMap h a) (newDart h a)).SameCycle
    (oldEmbedding h a d) (oldEmbedding h a d')
  have hstep : ∀ x₁ x₂, FaceClassStep M (· ∈ Set.range e) x₁ x₂ →
      FaceClassStep M (· ∈ Set.range (ambientEmbedding h a)) x₁ x₂ ∨
        (x₁ = a ∧ x₂ = M.alpha a) ∨ (x₁ = M.alpha a ∧ x₂ = a) := by
    rintro x₁ x₂ (hx | ⟨hx₁, hx⟩)
    · exact Or.inl (Or.inl hx)
    · by_cases hxa : x₁ = a
      · exact Or.inr (Or.inl ⟨hxa, hx.trans (congrArg M.alpha hxa)⟩)
      · by_cases hxb : x₁ = M.alpha a
        · exact Or.inr (Or.inr ⟨hxb, by rw [hx, hxb, M.alpha_involutive]⟩)
        · refine Or.inl (Or.inr ⟨?_, hx⟩)
          rintro ⟨z, rfl⟩
          rcases z.2 with hz | hz | hz
          · exact hx₁ hz
          · exact hxa hz
          · exact hxb hz
  rcases eqvGen_cases_of_pair hstep hp with hr | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact hjoin hd hd' (hsc (oldEmbedding h a d) (oldEmbedding h a d') hr)
  · have h₁' := hsc (oldEmbedding h a d) (newDart h a) h₁
    have h₂' := hsc ((toCombMap h a).alpha (newDart h a)) (oldEmbedding h a d') h₂
    by_cases hface : (toCombMap h a).faceOf (newDart h a) =
        (toCombMap h a).faceOf ((toCombMap h a).alpha (newDart h a))
    · exact hjoin hd hd'
        (h₁'.trans ((((toCombMap h a).faceOf_eq_iff _ _).mp hface).trans h₂'))
    · exact (EdgeDeletion.joinedFacePerm_of_sameCycle _ _ hface h₁').trans
        ((EdgeDeletion.joinedFacePerm_sameCycle _ _ hface).trans
          (EdgeDeletion.joinedFacePerm_of_sameCycle _ _ hface h₂'))
  · have h₁' := hsc (oldEmbedding h a d) ((toCombMap h a).alpha (newDart h a)) h₁
    have h₂' := hsc (newDart h a) (oldEmbedding h a d') h₂
    by_cases hface : (toCombMap h a).faceOf (newDart h a) =
        (toCombMap h a).faceOf ((toCombMap h a).alpha (newDart h a))
    · exact hjoin hd hd'
        (h₁'.trans ((((toCombMap h a).faceOf_eq_iff _ _).mp hface).symm.trans h₂'))
    · exact (EdgeDeletion.joinedFacePerm_of_sameCycle _ _ hface h₁').trans
        ((EdgeDeletion.joinedFacePerm_sameCycle _ _ hface).symm.trans
          (EdgeDeletion.joinedFacePerm_of_sameCycle _ _ hface h₂'))

end CombMap.RestrictionGrowth

namespace CombMap.IsRestriction

variable {M : CombMap.{u}} {N : CombMap.{v}} {e : N.Dart ↪ M.Dart}

/-- Growth induction over cores in the ambient universe. -/
theorem faceOf_eq_of_faceClass_aux (hM : M.IsPlanar) (n : ℕ) :
    ∀ (K : CombMap.{u}) (f : K.Dart ↪ M.Dart), M.dartCount - K.dartCount = n →
      M.IsRestriction K f → K.IsConnected → ∀ x y : K.Dart,
        Relation.EqvGen (FaceClassStep M (· ∈ Set.range f)) (f x) (f y) →
          K.faceOf x = K.faceOf y := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro K f hcount hf hK x y hp
      by_cases hsurj : Function.Surjective f
      · exact (K.faceOf_eq_iff x y).mpr
          ((hf.facePerm_sameCycle_iff_of_surjective hsurj x y).mpr
            (M.facePerm_sameCycle_of_faceClass hp fun z => hsurj z))
      · obtain ⟨b, hb⟩ := hf.exists_sigma_frontier hM.1 x hsurj
        have hv : M.vertexOf (M.sigma (f b)) = M.vertexOf (f b) := M.vertexOf_sigma (f b)
        have hcard := RestrictionGrowth.dartCount_add_two hf (M.sigma (f b)) hb
        have hle : (RestrictionGrowth.toCombMap hf (M.sigma (f b))).dartCount ≤ M.dartCount :=
          Nat.card_le_card_of_injective _
            (RestrictionGrowth.ambientEmbedding hf (M.sigma (f b))).injective
        have hlt :
            M.dartCount - (RestrictionGrowth.toCombMap hf (M.sigma (f b))).dartCount < n := by
          omega
        exact RestrictionGrowth.faceOf_eq_of_grown hf (M.sigma (f b)) hM hK hb b hv
          (ih _ hlt _ _ rfl (RestrictionGrowth.ambientRestriction hf _)
            (RestrictionGrowth.connected hf _ hK b hv)) hp

/-- Face classes of a connected planar restriction: advancing around ambient
faces and crossing ambient edges that are not retained never passes between two
different faces of the retained map. -/
theorem faceOf_eq_of_faceClass (h : M.IsRestriction N e) (hM : M.IsPlanar)
    (hN : N.IsConnected) {d d' : N.Dart}
    (hp : Relation.EqvGen (FaceClassStep M (· ∈ Set.range e)) (e d) (e d')) :
    N.faceOf d = N.faceOf d' := by
  classical
  by_cases hsurj : Function.Surjective e
  · exact (N.faceOf_eq_iff d d').mpr
      ((h.facePerm_sameCycle_iff_of_surjective hsurj d d').mpr
        (M.facePerm_sameCycle_of_faceClass hp fun z => hsurj z))
  · obtain ⟨b, hb⟩ := h.exists_sigma_frontier hM.1 d hsurj
    have hv : M.vertexOf (M.sigma (e b)) = M.vertexOf (e b) := M.vertexOf_sigma (e b)
    exact RestrictionGrowth.faceOf_eq_of_grown h (M.sigma (e b)) hM hN hb b hv
      (faceOf_eq_of_faceClass_aux hM _ _ _ rfl (RestrictionGrowth.ambientRestriction h _)
        (RestrictionGrowth.connected h _ hN b hv)) hp

end CombMap.IsRestriction

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.eqvGen_cases_of_pair
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.IsRestriction.facePerm_sameCycle_iff_of_surjective
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.faceOf_ne_of_planar
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.joinedFacePerm_sameCycle_of_planar
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.RestrictionGrowth.faceOf_eq_of_grown
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.IsRestriction.faceOf_eq_of_faceClass
