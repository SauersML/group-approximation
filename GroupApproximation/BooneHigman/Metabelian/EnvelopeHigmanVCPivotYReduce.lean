import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCPivotYComplete
import GroupApproximation.Meta.AxiomGuard

/-!
# Complete deep pivot closure (lane bh-met-77u)

Notation as in `EnvelopeHigmanVCTreeNFWitPivot`: `Q = higmanVCCommon_Q d`, `H_C` is the image of
the antichain subgroup on `C`, and `S = U · ⋃_C H_C · U` with `U` the balanced subgroup.

`higmanVCPivotY_Closed d L t` is `higmanVCPivotAC_Closed d L t` restricted to antichains `C`
that are complete at some depth `M`: every word of length `M` has a prefix in `C`.

`HigmanVCPivotYStatement` (Z) is `HigmanVCPivotACStatement` (Y) with that closure.

* `higmanVCPivotY_Y_of_Z : Z → Y`, the reduction.  It completes `C` (see
  `EnvelopeHigmanVCPivotYComplete`) and uses `H_C ≤ H_{C ∪ fill}`.
* `higmanVCPivotY_Z_of_Y : Y → Z`.  **LOUD: Z is equivalent to Y as a Prop.**  Z is smaller in
  proof content only.  A prover of Z may assume that `C` tiles the cones of both `a` and `b` at
  depth `M` by words extending `a` and `b` (`higmanVCPivotY_cone_cover`).  Without completeness,
  the cones of `a` and `b` need not be covered by `C`.

**Truth.**  Z ⇔ Y ⇔ X = `HigmanVCTreeNFWitPivotStatement` (lane bh-met-77s).  All three imply
Higman's relation completeness (1) for `V_d` (`higmanVCPivotAC_ker_le_of_Y`), so they are
Higman-strength.  They are not proved here.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Deep pivot closure over antichains that are complete at some depth. -/
def higmanVCPivotY_Closed (d L : ℕ) (t : higmanVCCommon_Q d) : Prop :=
  ∀ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C → (∀ c ∈ C, L ≤ c.length) →
    (∃ M : ℕ, ∀ w : List (Fin d), w.length = M → ∃ c ∈ C, c <+: w) →
      ∀ h ∈ higmanVCTreeNFWitPivot_H d C, h * t ∈ higmanVCTreeNFWitPivot_S d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_Closed

/-- **The residual Statement Z**: complete deep antichain pivot closure of the concrete pivots.
LOUD: equivalent to `HigmanVCPivotACStatement` as a Prop (`higmanVCPivotY_Z_of_Y`). -/
def HigmanVCPivotYStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a b : List (Fin d), a.length = n ∧
    b.length = n + 1 ∧ ¬ a <+: b ∧ ¬ b <+: a ∧
      higmanVCPivotY_Closed d (n + 1) (higmanVCCommon_mk d (FreeGroup.of (a, b)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCPivotYStatement

/-- **The completion step.**  Closure over complete antichains gives closure over all deep
antichains. -/
theorem higmanVCPivotY_ACClosed_of_Closed {d L : ℕ} {t : higmanVCCommon_Q d}
    (ht : higmanVCPivotY_Closed d L t) : higmanVCPivotAC_Closed d L t := by
  intro C hC hlen h hh
  have hL : ∀ c ∈ C, c.length ≤ max L (C.sup List.length) :=
    fun c hc => le_max_of_le_right (Finset.le_sup (f := List.length) hc)
  exact ht (higmanVCPivotY_complete C (max L (C.sup List.length)))
    (higmanVCPivotY_complete_isAC hC hL)
    (higmanVCPivotY_complete_length hlen (le_max_left _ _))
    ⟨_, higmanVCPivotY_complete_cover C _⟩ h
    (higmanVCPivotY_H_mono (higmanVCPivotY_subset_complete C _) hh)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_ACClosed_of_Closed

/-- Closure over all deep antichains gives closure over complete ones (forget completeness). -/
theorem higmanVCPivotY_Closed_of_ACClosed {d L : ℕ} {t : higmanVCCommon_Q d}
    (ht : higmanVCPivotAC_Closed d L t) : higmanVCPivotY_Closed d L t :=
  fun C hC hlen _ h hh => ht C hC hlen h hh

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_Closed_of_ACClosed

/-- **Endpoint**: Z gives Y. -/
theorem higmanVCPivotY_Y_of_Z (h : HigmanVCPivotYStatement) : HigmanVCPivotACStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, ht⟩ := h d hd N
  exact ⟨n, hn, a, b, ha, hb, hab, hba, higmanVCPivotY_ACClosed_of_Closed ht⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_Y_of_Z

/-- **LOUD**: Y gives Z, so Z is equivalent to Y as a Prop. -/
theorem higmanVCPivotY_Z_of_Y (h : HigmanVCPivotACStatement) : HigmanVCPivotYStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, ht⟩ := h d hd N
  exact ⟨n, hn, a, b, ha, hb, hab, hba, higmanVCPivotY_Closed_of_ACClosed ht⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_Z_of_Y

/-- **Endpoint**: Z gives X. -/
theorem higmanVCPivotY_X_of_Z (h : HigmanVCPivotYStatement) :
    HigmanVCTreeNFWitPivotStatement :=
  higmanVCPivotAC_X_of_Y (higmanVCPivotY_Y_of_Z h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_X_of_Z

/-- **Endpoint**: Z gives (1) at every `d > 1`. -/
theorem higmanVCPivotY_ker_le_of_Z (h : HigmanVCPivotYStatement) (d : ℕ) (hd : 1 < d) :
    (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) :=
  higmanVCPivotAC_ker_le_of_Y (higmanVCPivotY_Y_of_Z h) d hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_ker_le_of_Z

end GroupApproximation.BooneHigman.Metabelian.Envelope
