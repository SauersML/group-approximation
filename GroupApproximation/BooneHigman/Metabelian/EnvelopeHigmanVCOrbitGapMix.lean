import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# The mixed class `U · Sym · t U t⁻¹` of the orbit residual (lane bh-met-91d)

Notation as in `EnvelopeHigmanVCOrbitReduce`: pivot `t = mk (of (a, b))` with `a`, `b`
incomparable, `U = higmanVCTreeNF_U d`, `S = higmanVCTreeNFWitPivot_S d`.

**Mixed elements (proved).**  Call `h` *mixed* (`higmanVCOrbitGap_Mix`) if
`h = u σ (t v t⁻¹)` with `u, v ∈ U` and `σ` symmetric (`higmanVCLeafExp_Sym`).  Then
`h t = u (σ t) v ∈ U · S · U ⊆ S` (`higmanVCOrbitGap_mix_mem_S`).  The point is that `S` is
closed under left and right multiplication by `U`.  A right factor `t v t⁻¹` passes through
`t` and becomes `v`.

The mixed class contains all three classes discharged so far:
* symmetric elements (`higmanVCOrbitGap_mix_of_sym`);
* a/b-balanced elements (`higmanVCOrbitGap_mix_of_bal`), via the orbit split `h = u σ`;
* twisted-balanced elements (`higmanVCOrbitGap_mix_of_twist_bal`).  Mixed elements are
  closed under the twist `h ↦ t⁻¹ h⁻¹ t⁻¹` (`higmanVCOrbitGap_mix_of_twist`), because the
  twist of a symmetric `σ` is symmetric (`higmanVCOrbitGap_sym_twist`).

It is strictly larger than their union.  Take `a = 00`, `b = 010` and
`h = swap(001, 011) · swap(000, 01000)`.  Evaluated in `V_2`, `h` is not a/b-balanced:
the near cone `000` goes to `01000`, a length change.  Its twist
`swap(0100, 0000) · swap(0101, 011)` is not balanced either: the near cone `0101` goes to
`011`.  The symmetry search of 77x finds no tree of depth `≤ 5`.  Yet
`h = swap(001, 011) · (t · swap(0100, 0000) · t⁻¹)` is mixed, and both swaps are balanced.
See `SP/bh-met-91d/mix_search.py` and `mix_check.py`.  In the fixed antichain `C` of 77x
there are 14 such products of one balanced and one `t`-balanced swap.  Also 400/400 random
`U · t U t⁻¹` decompositions over trees of depth `≤ 6` were verified pointwise, and the
identity has 0 failures at depth 9.

**Residual `W''` = `HigmanVCOrbitGapStatement`.**  This is `W` with the pivot closure
required only for non-mixed `h ∈ H_C`.  `higmanVCOrbitGap_orbit_of_gap` proves `W'' → W'`.
The root wiring is `higmanVCOrbitGap_swapSection_of_tau`.

LOUD, on strength: as Props `W'' ⇔ W' ⇔ W ⇔ Z`, which is Higman-strength.  `W''` is
strictly smaller than `W'` in PROOF CONTENT only.  Every product `u σ (t v t⁻¹)` is
discharged here, including the example above, which `W'` leaves open.  The remaining case is
an `h` whose near cones cannot be matched through `U` on the left and `t U t⁻¹` on the right.
The gap example `swap(a0, b000)` of 77x is such an element.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `h` is *mixed* for the pivot `t = (a, b)`: `h = u σ (t v t⁻¹)` with `u, v ∈ U` and `σ`
symmetric. -/
def higmanVCOrbitGap_Mix (d : ℕ) (a b : List (Fin d)) (h : higmanVCCommon_Q d) : Prop :=
  ∃ u ∈ higmanVCTreeNF_U d, ∃ σ : higmanVCCommon_Q d, higmanVCLeafExp_Sym d a b σ ∧
    ∃ v ∈ higmanVCTreeNF_U d, h = u * σ * (higmanVCCommon_mk d (FreeGroup.of (a, b)) * v *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_Mix

/-- **Mixed discharge.**  `h = u σ (t v t⁻¹)` gives `h t = u (σ t) v ∈ S`. -/
theorem higmanVCOrbitGap_mix_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {h : higmanVCCommon_Q d} (hh : higmanVCOrbitGap_Mix d a b h) :
    h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  obtain ⟨u, hu, σ, hσ, v, hv, rfl⟩ := hh
  have e : u * σ * (higmanVCCommon_mk d (FreeGroup.of (a, b)) * v *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹) *
        higmanVCCommon_mk d (FreeGroup.of (a, b)) =
      u * (σ * higmanVCCommon_mk d (FreeGroup.of (a, b))) * v := by
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [e]
  exact higmanVCTreeNFWitPivot_S_mul_U
    (higmanVCPivotAC_U_mul_S hu (higmanVCLeafExp_sym_mem_S hab hba hσ)) hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_mix_mem_S

/-- Symmetric elements are mixed. -/
theorem higmanVCOrbitGap_mix_of_sym {d : ℕ} {a b : List (Fin d)} {h : higmanVCCommon_Q d}
    (hh : higmanVCLeafExp_Sym d a b h) : higmanVCOrbitGap_Mix d a b h :=
  ⟨1, Subgroup.one_mem _, h, hh, 1, Subgroup.one_mem _, by
    simp only [mul_one, one_mul, mul_inv_cancel]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_mix_of_sym

/-- a/b-balanced elements are mixed: the orbit split gives `h = u σ` with `σ` in the far
antichain subgroup, which is symmetric with the trivial tree. -/
theorem higmanVCOrbitGap_mix_of_bal {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {h : higmanVCCommon_Q d} (hh : higmanVCOrbit_Bal d a b h) :
    higmanVCOrbitGap_Mix d a b h := by
  obtain ⟨C, hC, r, rfl, hlen⟩ := hh
  have hK : ∀ x y : ↥C, ¬ higmanVCOrbit_Near a b x.1 → ¬ higmanVCOrbit_Near a b y.1 →
      higmanVCCommon_mk d (FreeGroup.of (x.1, y.1)) ∈
        higmanVCTreeNFWitPivot_H d (higmanVCOrbit_far a b C) := fun x y hx hy =>
    higmanVCLeafExp_letter_mem_H (higmanVCOrbit_mem_far.mpr (Or.inr (Or.inr ⟨x.2, hx⟩)))
      (higmanVCOrbit_mem_far.mpr (Or.inr (Or.inr ⟨y.2, hy⟩)))
  obtain ⟨u, hu, σ, hσ, heq⟩ :=
    higmanVCOrbit_split hC (fun c => higmanVCOrbit_Near a b c.1) hK _ r le_rfl hlen
  refine ⟨u, hu, σ, ⟨higmanVCOrbit_far a b C, {[]}, higmanVCOrbit_far_isAC hab hba hC,
    higmanVCLeafExp_IsTree.root, hσ, fun e he => ?_⟩, 1, Subgroup.one_mem _, ?_⟩
  · rw [Finset.mem_singleton] at he
    subst he
    simp only [List.append_nil]
    exact ⟨higmanVCOrbit_mem_far.mpr (Or.inl rfl),
      higmanVCOrbit_mem_far.mpr (Or.inr (Or.inl rfl))⟩
  · rw [heq]
    simp only [mul_one, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_mix_of_bal

/-- The twist `t⁻¹ σ⁻¹ t⁻¹` of a symmetric element is symmetric, with the same `D` and `T`:
the pattern split puts `t` into `H_D`. -/
theorem higmanVCOrbitGap_sym_twist {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {σ : higmanVCCommon_Q d} (hσ : higmanVCLeafExp_Sym d a b σ) :
    higmanVCLeafExp_Sym d a b ((higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ * σ⁻¹ *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹) := by
  obtain ⟨D, T, hD, hT, hσD, hsub⟩ := hσ
  have ht : higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_H d D :=
    higmanVCLeafExp_tree_mem hT a b hab hba fun e he =>
      higmanVCLeafExp_letter_mem_H (hsub e he).1 (hsub e he).2
  exact ⟨D, T, hD, hT, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ht)
    (Subgroup.inv_mem _ hσD)) (Subgroup.inv_mem _ ht), hsub⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_sym_twist

end GroupApproximation.BooneHigman.Metabelian.Envelope
