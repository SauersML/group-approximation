import GroupApproximation.GGT.VanKampen.CombMapInvariantRestrict
import GroupApproximation.GGT.VanKampen.CombMapRestrictionPlanarity
import GroupApproximation.GGT.VanKampen.CombMapEulerSmallFaceBudget
import GroupApproximation.Meta.AxiomGuard

/-!
# Euler's count on a restriction of a planar map, component by component

A restriction of a planar map need not be connected, but each of its components is a connected
restriction of the planar map, hence planar (`IsRestriction.planar`).  Splitting off the component
of one dart with `CombMap.restrict` adds Euler characteristics
(`eulerCharacteristic_restrict_add`), so a nonempty restriction has Euler characteristic at least
two.  The face half of the small-face budget, `six_mul_faceCount_le`, holds for any map, so the
budget `2E + 6 ≤ 3V + t` holds on every nonempty restriction of a planar map whose faces have
degree at least four.

* `CombMap.restrict_isRestriction_subtype`: an invariant restriction is a restriction.
* `CombMap.eulerCharacteristic_eq_zero_of_dartEmpty`: a map with no darts has Euler characteristic
  zero.
* `CombMap.two_le_eulerCharacteristic_of_isRestriction`: `2 ≤ χ` on a nonempty restriction of a
  planar map.
* `CombMap.two_mul_edgeCount_add_six_le_of_isRestriction`: the small-face budget there.

Model test (hand).  Two disjoint squares with their inner faces, as a restriction of a planar map:
`χ = 4 ≥ 2`, and `2·8 + 6 = 22 ≤ 3·8 + 4 = 28`.

## Manuscript status

Infrastructure for `thm:hull` (through the contact count of Osin's Lemma 9.4,
arXiv:math/0411039v3, §9); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap

universe u

/-- **An invariant restriction is a restriction**: reversal is unchanged and the vertex rotation
already returns in one step. -/
theorem restrict_isRestriction_subtype (M : CombMap.{u}) (S : M.Dart → Prop)
    (hα : ∀ x, S (M.alpha x) ↔ S x) (hσ : ∀ x, S (M.sigma x) ↔ S x) :
    M.IsRestriction (M.restrict S hα hσ) (Function.Embedding.subtype S) where
  alpha_map _ := rfl
  sigma_firstReturn b :=
    ⟨1, Nat.one_pos, by rw [pow_one]; rfl, fun k hk hk1 => absurd hk1 (by omega)⟩

/-- A map with no darts has Euler characteristic zero. -/
theorem eulerCharacteristic_eq_zero_of_dartEmpty (M : CombMap.{u}) (h : IsEmpty M.Dart) :
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

/-- **A nonempty restriction of a planar map has Euler characteristic at least two**, one planar
component at a time. -/
theorem two_le_eulerCharacteristic_of_isRestriction {A : CombMap.{u}} (hA : A.IsPlanar) :
    ∀ (n : ℕ) (M : CombMap.{u}) (e : M.Dart ↪ A.Dart), A.IsRestriction M e →
      M.dartCount = n → Nonempty M.Dart → 2 ≤ M.eulerCharacteristic := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M e he hn hne
    classical
    obtain ⟨x₀⟩ := hne
    let S : M.Dart → Prop := fun x => Relation.EqvGen M.Adjacent x₀ x
    have hα : ∀ x, S (M.alpha x) ↔ S x := fun x =>
      ⟨fun h => h.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive x))),
        fun h => h.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl))⟩
    have hσ : ∀ x, S (M.sigma x) ↔ S x := fun x =>
      ⟨fun h => h.trans _ _ _ (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr rfl))),
        fun h => h.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inr rfl))⟩
    have hK : (M.restrict S hα hσ).IsConnected :=
      M.restrict_connected S hα hσ (Relation.EqvGen.refl x₀) (fun _ hx => hx)
    have hKp : (M.restrict S hα hσ).IsPlanar :=
      (he.trans (M.restrict_isRestriction_subtype S hα hσ)).planar hA hK
        ⟨x₀, Relation.EqvGen.refl x₀⟩
    have hsplit := M.eulerCharacteristic_restrict_add S hα hσ
    have hK2 := hKp.2
    by_cases hrest : Nonempty {x // ¬ S x}
    · have hlt : (M.restrict (fun x => ¬ S x) (M.compl_alpha S hα)
          (M.compl_sigma S hσ)).dartCount < n := by
        rw [← hn]
        show Nat.card {x // ¬ S x} < Nat.card M.Dart
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_subtype_lt (p := fun x => ¬ S x) (x := x₀)
          (not_not.mpr (Relation.EqvGen.refl x₀))
      have h2 := ih _ hlt _ _
        (he.trans (M.restrict_isRestriction_subtype (fun x => ¬ S x) (M.compl_alpha S hα)
          (M.compl_sigma S hσ))) rfl hrest
      linarith
    · have h0 : (M.restrict (fun x => ¬ S x) (M.compl_alpha S hα)
          (M.compl_sigma S hσ)).eulerCharacteristic = 0 :=
        eulerCharacteristic_eq_zero_of_dartEmpty _ (not_nonempty_iff.mp hrest)
      linarith

/-- **The small-face budget on a restriction of a planar map.**  On a nonempty restriction of a
planar map with every face of degree at least four, `2E + 6 ≤ 3V + t`. -/
theorem two_mul_edgeCount_add_six_le_of_isRestriction {A : CombMap.{u}} (hA : A.IsPlanar)
    {M : CombMap.{u}} {e : M.Dart ↪ A.Dart} (he : A.IsRestriction M e) (hne : Nonempty M.Dart)
    (hfour : ∀ f : M.Face, 4 ≤ M.faceDegree f) :
    2 * M.edgeCount + 6 ≤
      3 * M.vertexCount + (Finset.univ.filter fun f : M.Face => M.faceDegree f < 6).card := by
  have hχ := two_le_eulerCharacteristic_of_isRestriction hA _ M e he rfl hne
  have hb := M.six_mul_faceCount_le hfour
  unfold CombMap.eulerCharacteristic at hχ
  omega

end GroupApproximation.GGT.VanKampen.CombMap

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.restrict_isRestriction_subtype
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.two_le_eulerCharacteristic_of_isRestriction
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.two_mul_edgeCount_add_six_le_of_isRestriction
