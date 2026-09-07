import GroupApproximation.GGT.VanKampen.CombMapEdgeDeletion
import GroupApproximation.GGT.VanKampen.CombMapSimpleEuler

/-!
# Euler characteristic after deleting one edge

The exact count identities account for every disappearing vertex. In a
connected map with a retained dart, at most one vertex disappears. If the
two sides of the deleted edge are different faces, no vertex disappears.
Consequently this actual edge deletion cannot lower Euler characteristic.
Connectedness of the result and iteration over a region are separate steps.
-/

namespace GroupApproximation.GGT.VanKampen

namespace CombMap

/-- If vertex rotation swaps the two darts of an edge, their component
contains no other dart. -/
theorem dart_eq_or_alpha_of_swapped_endpoints (M : CombMap)
    (hM : M.IsConnected) (a : M.Dart)
    (ha : M.sigma a = M.alpha a) (hb : M.sigma (M.alpha a) = a) (x : M.Dart) :
    x = a ∨ x = M.alpha a := by
  let P : M.Dart → Prop := fun d => d = a ∨ d = M.alpha a
  have hα : ∀ d, P (M.alpha d) ↔ P d := by
    intro d
    constructor
    · rintro (h | h)
      · exact Or.inr ((M.alpha_involutive d).symm.trans (congrArg M.alpha h))
      · exact Or.inl (M.alpha.injective h)
    · rintro (rfl | rfl)
      · exact Or.inr rfl
      · exact Or.inl (M.alpha_involutive a)
  have hσ : ∀ d, P (M.sigma d) ↔ P d := by
    intro d
    constructor
    · rintro (h | h)
      · exact Or.inr (M.sigma.injective (h.trans hb.symm))
      · exact Or.inl (M.sigma.injective (h.trans ha.symm))
    · rintro (rfl | rfl)
      · exact Or.inr ha
      · exact Or.inl hb
  have hclosure : ∀ d e, Relation.EqvGen M.Adjacent d e → (P d ↔ P e) := by
    intro d e h
    induction h with
    | rel d e h =>
        rcases h with rfl | rfl
        · exact (hα d).symm
        · exact (hσ d).symm
    | refl d => rfl
    | symm d e _ ih => exact ih.symm
    | trans d e f _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (hclosure a x (hM a x)).mp (Or.inl rfl)

end CombMap

namespace EdgeDeletion

open Equiv PermOrbitErasePoint
universe u
variable (M : CombMap.{u}) [DecidableEq M.Dart] (a : M.Dart)

theorem euler_balance_of_sameFace (hface : M.faceOf a = M.faceOf (M.alpha a)) :
    (toCombMap M a).eulerCharacteristic + 2 * (M.vertexCount : ℤ) =
      M.eulerCharacteristic + 2 * ((toCombMap M a).vertexCount : ℤ) + 2 := by
  have hf : ((toCombMap M a).faceCount : ℤ) + M.vertexCount =
      (toCombMap M a).vertexCount + M.faceCount + 1 := by
    exact_mod_cast faceCount_balance_of_sameFace M a hface
  have he : ((toCombMap M a).edgeCount : ℤ) + 1 = M.edgeCount := by
    exact_mod_cast edgeCount_add_one M a
  unfold CombMap.eulerCharacteristic
  omega

theorem euler_balance_of_neFace (hface : M.faceOf a ≠ M.faceOf (M.alpha a)) :
    (toCombMap M a).eulerCharacteristic + 2 * (M.vertexCount : ℤ) =
      M.eulerCharacteristic + 2 * ((toCombMap M a).vertexCount : ℤ) := by
  have hf : ((toCombMap M a).faceCount : ℤ) + M.vertexCount + 1 =
      (toCombMap M a).vertexCount + M.faceCount := by
    exact_mod_cast faceCount_balance_of_neFace M a hface
  have he : ((toCombMap M a).edgeCount : ℤ) + 1 = M.edgeCount := by
    exact_mod_cast edgeCount_add_one M a
  unfold CombMap.eulerCharacteristic
  omega

omit [DecidableEq M.Dart] in
/-- In a connected map with some retained dart, both endpoints cannot be
separate degree-one vertices. -/
theorem not_both_fixed (hM : M.IsConnected) (d : Dart M a) :
    ¬ (M.sigma a = a ∧ M.sigma (M.alpha a) = M.alpha a) := by
  rintro ⟨ha, hb⟩
  rcases M.dart_eq_or_alpha_of_fixed_endpoints hM a ha hb (value M a d) with h | h
  · exact value_ne M a d h
  · exact value_ne_reverse M a d h

theorem vertexCount_loss_le_one (hM : M.IsConnected) (d : Dart M a) :
    M.vertexCount ≤ (toCombMap M a).vertexCount + 1 := by
  by_cases ha : M.sigma a = a
  · have hb : M.sigma (M.alpha a) ≠ M.alpha a :=
      fun hb => not_both_fixed M a hM d ⟨ha, hb⟩
    have hb' : erase M.sigma a (reverseDart M a) ≠ reverseDart M a := by
      intro h
      have hv := congrArg Subtype.val h
      change Equiv.swap a (M.sigma a) (M.sigma (M.alpha a)) = M.alpha a at hv
      rw [ha, Equiv.swap_self] at hv
      exact hb hv
    have h₁ : Nat.card (CombMap.Orbit (erase M.sigma a)) + 1 = M.vertexCount :=
      orbit_card_of_fixed M.sigma a ha
    have h₂ : (toCombMap M a).vertexCount = Nat.card (CombMap.Orbit (erase M.sigma a)) :=
      orbit_card_of_not_fixed (erase M.sigma a) (reverseDart M a) hb'
    omega
  · have h₁ : Nat.card (CombMap.Orbit (erase M.sigma a)) = M.vertexCount :=
      orbit_card_of_not_fixed M.sigma a ha
    by_cases hb : erase M.sigma a (reverseDart M a) = reverseDart M a
    · have h₂ : (toCombMap M a).vertexCount + 1 = Nat.card (CombMap.Orbit (erase M.sigma a)) :=
        orbit_card_of_fixed (erase M.sigma a) (reverseDart M a) hb
      omega
    · have h₂ : (toCombMap M a).vertexCount = Nat.card (CombMap.Orbit (erase M.sigma a)) :=
        orbit_card_of_not_fixed (erase M.sigma a) (reverseDart M a) hb
      omega

omit [DecidableEq M.Dart] in
/-- Different face sides rule out degree-one endpoints. -/
theorem sigma_ne_of_neFace (hface : M.faceOf a ≠ M.faceOf (M.alpha a)) :
    M.sigma a ≠ a ∧ M.sigma (M.alpha a) ≠ M.alpha a := by
  constructor
  · intro h
    have hp : M.facePerm (M.alpha a) = a := by
      change M.sigma (M.alpha (M.alpha a)) = a
      rw [M.alpha_involutive, h]
    have hf := M.faceOf_facePerm (M.alpha a)
    rw [hp] at hf
    exact hface hf
  · intro h
    have hp : M.facePerm a = M.alpha a := h
    have hf := M.faceOf_facePerm a
    rw [hp] at hf
    exact hface hf.symm

/-- A deleted edge between different faces retains every old vertex, unless
it was the entire connected map. A retained dart excludes that exception. -/
theorem vertexCount_eq_of_neFace (hM : M.IsConnected) (d : Dart M a)
    (hface : M.faceOf a ≠ M.faceOf (M.alpha a)) :
    (toCombMap M a).vertexCount = M.vertexCount := by
  obtain ⟨ha, hb⟩ := sigma_ne_of_neFace M a hface
  have hb' : erase M.sigma a (reverseDart M a) ≠ reverseDart M a := by
    intro h
    have hv := congrArg Subtype.val h
    change Equiv.swap a (M.sigma a) (M.sigma (M.alpha a)) = M.alpha a at hv
    by_cases hba : M.sigma (M.alpha a) = a
    · rw [hba, Equiv.swap_apply_left] at hv
      rcases M.dart_eq_or_alpha_of_swapped_endpoints hM a hv hba (value M a d) with hd | hd
      · exact value_ne M a d hd
      · exact value_ne_reverse M a d hd
    · rw [Equiv.swap_apply_of_ne_of_ne hba
        (M.sigma.injective.ne (M.alpha_fixedPointFree a))] at hv
      exact hb hv
  exact (orbit_card_of_not_fixed (erase M.sigma a) (reverseDart M a) hb').trans
    (orbit_card_of_not_fixed M.sigma a ha)

theorem euler_eq_of_neFace (hM : M.IsConnected) (d : Dart M a)
    (hface : M.faceOf a ≠ M.faceOf (M.alpha a)) :
    (toCombMap M a).eulerCharacteristic = M.eulerCharacteristic := by
  have h := euler_balance_of_neFace M a hface
  rw [vertexCount_eq_of_neFace M a hM d hface] at h
  omega

/-- A single edge deletion with a nonempty remainder cannot lower Euler
characteristic in a connected map. This does not assert connectedness of the
remainder or preservation of Euler characteristic in every case. -/
theorem eulerCharacteristic_le_deleted (hM : M.IsConnected) (d : Dart M a) :
    M.eulerCharacteristic ≤ (toCombMap M a).eulerCharacteristic := by
  by_cases hface : M.faceOf a = M.faceOf (M.alpha a)
  · have h := euler_balance_of_sameFace M a hface
    have hv : (M.vertexCount : ℤ) ≤ (toCombMap M a).vertexCount + 1 := by
      exact_mod_cast vertexCount_loss_le_one M a hM d
    omega
  · exact (euler_eq_of_neFace M a hM d hface).ge

end EdgeDeletion
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.vertexCount_loss_le_one
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.vertexCount_eq_of_neFace
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.euler_eq_of_neFace
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.eulerCharacteristic_le_deleted
