import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitGapMix
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Closure properties of the mixed class (lane bh-met-91d)

Notation as in `EnvelopeHigmanVCOrbitGapMix`.

* `higmanVCOrbitGap_mix_of_twist`: the mixed class is closed under `h ↦ t⁻¹ h⁻¹ t⁻¹`.  So
  twisted-balanced elements are mixed (`higmanVCOrbitGap_mix_of_twist_bal`).
* `higmanVCOrbitGap_U_mul_mix` and `higmanVCOrbitGap_mix_mul_conj`: the class is closed
  under `U` on the left and under `t U t⁻¹` on the right.
* `higmanVCOrbitGap_mix_of_U`: every element of `U` is mixed, since `1` is symmetric
  (`higmanVCOrbitGap_sym_one`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The group identity behind the twist closure. -/
theorem higmanVCOrbitGap_twist_eq {G : Type*} [Group G] {t h u σ v : G}
    (e : t⁻¹ * h⁻¹ * t⁻¹ = u * σ * (t * v * t⁻¹)) :
    h = v⁻¹ * (t⁻¹ * σ⁻¹ * t⁻¹) * (t * u⁻¹ * t⁻¹) :=
  calc h = t⁻¹ * (t⁻¹ * h⁻¹ * t⁻¹)⁻¹ * t⁻¹ := by group
    _ = t⁻¹ * (u * σ * (t * v * t⁻¹))⁻¹ * t⁻¹ := by rw [e]
    _ = v⁻¹ * (t⁻¹ * σ⁻¹ * t⁻¹) * (t * u⁻¹ * t⁻¹) := by group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_twist_eq

/-- **Twist closure.**  If the twist `t⁻¹ h⁻¹ t⁻¹` is mixed, so is `h`. -/
theorem higmanVCOrbitGap_mix_of_twist {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbitGap_Mix d a b ((higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ * h⁻¹ *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)) :
    higmanVCOrbitGap_Mix d a b h := by
  obtain ⟨u, hu, σ, hσ, v, hv, e⟩ := hh
  exact ⟨v⁻¹, Subgroup.inv_mem _ hv, _, higmanVCOrbitGap_sym_twist hab hba hσ, u⁻¹,
    Subgroup.inv_mem _ hu, higmanVCOrbitGap_twist_eq e⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_mix_of_twist

/-- Twisted-balanced elements are mixed. -/
theorem higmanVCOrbitGap_mix_of_twist_bal {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbit_Bal d a b ((higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ * h⁻¹ *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)) :
    higmanVCOrbitGap_Mix d a b h :=
  higmanVCOrbitGap_mix_of_twist hab hba (higmanVCOrbitGap_mix_of_bal hab hba hh)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_mix_of_twist_bal

/-- Left multiplication by `U` preserves the mixed class. -/
theorem higmanVCOrbitGap_U_mul_mix {d : ℕ} {a b : List (Fin d)} {g h : higmanVCCommon_Q d}
    (hg : g ∈ higmanVCTreeNF_U d) (hh : higmanVCOrbitGap_Mix d a b h) :
    higmanVCOrbitGap_Mix d a b (g * h) := by
  obtain ⟨u, hu, σ, hσ, v, hv, rfl⟩ := hh
  exact ⟨g * u, Subgroup.mul_mem _ hg hu, σ, hσ, v, hv, by simp only [mul_assoc]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_U_mul_mix

/-- Right multiplication by `t U t⁻¹` preserves the mixed class. -/
theorem higmanVCOrbitGap_mix_mul_conj {d : ℕ} {a b : List (Fin d)}
    {h w : higmanVCCommon_Q d} (hh : higmanVCOrbitGap_Mix d a b h)
    (hw : w ∈ higmanVCTreeNF_U d) :
    higmanVCOrbitGap_Mix d a b (h * (higmanVCCommon_mk d (FreeGroup.of (a, b)) * w *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)) := by
  obtain ⟨u, hu, σ, hσ, v, hv, rfl⟩ := hh
  exact ⟨u, hu, σ, hσ, v * w, Subgroup.mul_mem _ hv hw, by
    simp only [mul_assoc, inv_mul_cancel_left]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_mix_mul_conj

/-- `1` is symmetric, with `D = {a, b}` and the trivial tree. -/
theorem higmanVCOrbitGap_sym_one {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) : higmanVCLeafExp_Sym d a b 1 := by
  refine ⟨higmanVCOrbit_far a b ∅, {[]},
    higmanVCOrbit_far_isAC hab hba (higmanVCTreeNFWitPivot_IsAC_empty d),
    higmanVCLeafExp_IsTree.root, Subgroup.one_mem _, fun e he => ?_⟩
  rw [Finset.mem_singleton] at he
  subst he
  simp only [List.append_nil]
  exact ⟨higmanVCOrbit_mem_far.mpr (Or.inl rfl),
    higmanVCOrbit_mem_far.mpr (Or.inr (Or.inl rfl))⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_sym_one

/-- Every element of `U` is mixed. -/
theorem higmanVCOrbitGap_mix_of_U {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {g : higmanVCCommon_Q d} (hg : g ∈ higmanVCTreeNF_U d) :
    higmanVCOrbitGap_Mix d a b g :=
  ⟨g, hg, 1, higmanVCOrbitGap_sym_one hab hba, 1, Subgroup.one_mem _, by
    simp only [mul_one, mul_inv_cancel]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_mix_of_U

end GroupApproximation.BooneHigman.Metabelian.Envelope
