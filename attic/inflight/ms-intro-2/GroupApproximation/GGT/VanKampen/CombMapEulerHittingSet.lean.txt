import GroupApproximation.GGT.VanKampen.CombMapInvariantRestrict
import GroupApproximation.Meta.AxiomGuard

/-!
# The Euler characteristic is at most twice a component hitting set

`CombMap.eulerCharacteristic_le_two` bounds a connected map.  A finite map every component of
which meets a finite set `T` of darts has Euler characteristic at most `2 |T|`.  Split off the
component of a dart of `T` with `CombMap.restrict`.  The Euler characteristics add
(`eulerCharacteristic_restrict_add`), the component is connected (`restrict_connected`), and the
rest is met by the other darts of `T` (`exists_eqvGen_restrict`).

* `eulerCharacteristic_eq_zero_of_isEmpty`: a map with no darts has Euler characteristic zero.
* `eulerCharacteristic_le_two_mul_card_of_hitting`.

Calibration: two disjoint spheres have Euler characteristic `4`, so one dart of `T` per component
is needed.

Infrastructure for the cutting transitions of Osin's Lemma 9.4 (arXiv:math/0411039v3, §9);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap

open Equiv
open scoped Classical

universe u

/-- A map with no darts has Euler characteristic zero. -/
theorem eulerCharacteristic_eq_zero_of_isEmpty (M : CombMap.{u}) (h : IsEmpty M.Dart) :
    M.eulerCharacteristic = 0 := by
  have hv : M.vertexCount = 0 :=
    Nat.card_eq_zero.mpr (Or.inl ⟨fun q => Quotient.inductionOn' q fun x => h.elim x⟩)
  have he : M.edgeCount = 0 :=
    Nat.card_eq_zero.mpr (Or.inl ⟨fun q => Quotient.inductionOn' q fun x => h.elim x⟩)
  have hf : M.faceCount = 0 :=
    Nat.card_eq_zero.mpr (Or.inl ⟨fun q => Quotient.inductionOn' q fun x => h.elim x⟩)
  unfold CombMap.eulerCharacteristic
  rw [hv, he, hf]
  simp

theorem eulerCharacteristic_le_two_mul_of_hitting_aux (n : ℕ) :
    ∀ (M : CombMap.{u}) (T : Finset M.Dart), T.card ≤ n →
      (∀ x, ∃ t ∈ T, Relation.EqvGen M.Adjacent x t) → M.eulerCharacteristic ≤ 2 * (n : ℤ) := by
  induction n with
  | zero =>
    intro M T hT hhit
    have hTe : T = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hT)
    have hempty : IsEmpty M.Dart := ⟨fun x => by
      obtain ⟨t, ht, -⟩ := hhit x
      simp [hTe] at ht⟩
    rw [M.eulerCharacteristic_eq_zero_of_isEmpty hempty]
    simp
  | succ n ih =>
    intro M T hT hhit
    rcases T.eq_empty_or_nonempty with hTe | ⟨t, ht⟩
    · have hempty : IsEmpty M.Dart := ⟨fun x => by
        obtain ⟨t, ht, -⟩ := hhit x
        simp [hTe] at ht⟩
      rw [M.eulerCharacteristic_eq_zero_of_isEmpty hempty]
      push_cast
      omega
    · let S : M.Dart → Prop := fun x => Relation.EqvGen M.Adjacent t x
      have hα : ∀ x, S (M.alpha x) ↔ S x := fun x =>
        ⟨fun h => Relation.EqvGen.trans _ _ _ h
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl))),
          fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ (Or.inl rfl))⟩
      have hσ : ∀ x, S (M.sigma x) ↔ S x := fun x =>
        ⟨fun h => Relation.EqvGen.trans _ _ _ h
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr rfl))),
          fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ (Or.inr rfl))⟩
      have hconn : (M.restrict S hα hσ).IsConnected :=
        M.restrict_connected S hα hσ (Relation.EqvGen.refl t) fun _ h => h
      have h1 := eulerCharacteristic_le_two (M.restrict S hα hσ) hconn
      let T' : Finset (M.restrict (fun x => ¬ S x) (M.compl_alpha S hα)
          (M.compl_sigma S hσ)).Dart :=
        T.subtype fun x => ¬ S x
      have hcard : T'.card ≤ n := by
        have hsub : T.filter (fun x => ¬ S x) ⊆ T.erase t := by
          intro x hx
          obtain ⟨hxT, hxS⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_erase.mpr ⟨fun hxt => hxS (hxt ▸ Relation.EqvGen.refl t), hxT⟩
        have hsubcard : T'.card = (T.filter fun x => ¬ S x).card := Finset.card_subtype _ _
        rw [hsubcard]
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem ht] at this
        omega
      have hhit' : ∀ x : (M.restrict (fun x => ¬ S x) (M.compl_alpha S hα)
          (M.compl_sigma S hσ)).Dart,
          ∃ t' ∈ T', Relation.EqvGen (M.restrict (fun x => ¬ S x) (M.compl_alpha S hα)
            (M.compl_sigma S hσ)).Adjacent x t' := by
        intro x
        obtain ⟨s, hs, hxs⟩ := hhit x.1
        obtain ⟨hs', hpath⟩ := M.exists_eqvGen_restrict (fun x => ¬ S x) (M.compl_alpha S hα)
          (M.compl_sigma S hσ) hxs x.2
        exact ⟨⟨s, hs'⟩, Finset.mem_subtype.mpr hs, hpath⟩
      have h2 := ih _ T' hcard hhit'
      rw [← M.eulerCharacteristic_restrict_add S hα hσ]
      push_cast
      linarith

/-- **The Euler characteristic of a map is at most twice a set of darts meeting every
component.** -/
theorem eulerCharacteristic_le_two_mul_card_of_hitting (M : CombMap.{u}) (T : Finset M.Dart)
    (hT : ∀ x, ∃ t ∈ T, Relation.EqvGen M.Adjacent x t) :
    M.eulerCharacteristic ≤ 2 * (T.card : ℤ) :=
  eulerCharacteristic_le_two_mul_of_hitting_aux T.card M T le_rfl hT

end GroupApproximation.GGT.VanKampen.CombMap

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.eulerCharacteristic_le_two_mul_card_of_hitting
