import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCPivotACConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Removing the middle balanced factor from antichain pivot closure (lane bh-met-77s)

Notation as in `EnvelopeHigmanVCTreeNFWitPivot`: `Q = higmanVCCommon_Q d`, `U` the balanced
subgroup, `H_C` the antichain subgroups, `S = U · ⋃_C H_C · U`.  Statement X
(`HigmanVCTreeNFWitPivotStatement`) asks that `h * u * t ∈ S` for all antichains `C`,
`h ∈ H_C` and `u ∈ U`.

**The residual Statement Y (`HigmanVCPivotACStatement`).**  Y asks only that `h * t ∈ S`, and only
for antichains `C` all of whose words have length `≥ n + 1` (`higmanVCPivotAC_Closed`).  So there
is no middle `u`, and `C` is deep.

**The reduction (`higmanVCPivotAC_ACClosed_of_Closed`), proved in `Q` without (1).**
1. Write `u = mk g` (surjectivity).
2. `g⁻¹` has the push property at some threshold `N` (`higmanVCCommon_push`).
3. Refine `C` to depth `L + N` (`higmanVCPivotAC_H_le_refine`, by deep splitting).
4. Conjugate by `mk g⁻¹`.  This gives `u⁻¹ h u ∈ H_{C''}` for an antichain `C''` of words of length
   `≥ L` (`higmanVCPivotAC_conj_mem`).
5. Then `h * u * t = u * (u⁻¹ h u * t) ∈ U · S ⊆ S`.

**LOUD: Y is Lean-provably equivalent to X** (`higmanVCPivotAC_X_of_Y`, `higmanVCPivotAC_Y_of_X`).
So it is not weaker as a Prop.  It is smaller in proof content: the middle `U` and the shallow
antichains are removed by a real argument in `Q`.  Y is not on the forbidden list: it is not
`ker ≤ normalClosure`, Schreier, TreeLevel or PivotClosed for all `t`, and it does not assume (1).

**Truth.**  In `V_d`, Y is the case `u = 1` of X, so it follows from Claim F.  Directly: take a
random refinement `C` of the level-`(n + 1)` words and a random `σ ∈ Sym(C)`, and test
`σ · (a, b) ∈ B · Sym(A) · B`.  This passed 600/600 trials at `d = 2, 3` and `n = 1, 2, 3`
(`SP/bh-met-77s/y_check.py`).  **Remaining gap:** Y itself, which is Claim F in `Q` for the
products `h * t`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Deep antichain pivot closure: `h * t ∈ S` for `h ∈ H_C`, `C` an antichain of words of length
`≥ L`. -/
def higmanVCPivotAC_Closed (d L : ℕ) (t : higmanVCCommon_Q d) : Prop :=
  ∀ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C → (∀ c ∈ C, L ≤ c.length) →
    ∀ h ∈ higmanVCTreeNFWitPivot_H d C, h * t ∈ higmanVCTreeNFWitPivot_S d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_Closed

/-- **The residual Statement Y**: deep antichain pivot closure of the concrete pivots. -/
def HigmanVCPivotACStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a b : List (Fin d), a.length = n ∧
    b.length = n + 1 ∧ ¬ a <+: b ∧ ¬ b <+: a ∧
      higmanVCPivotAC_Closed d (n + 1) (higmanVCCommon_mk d (FreeGroup.of (a, b)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCPivotACStatement

theorem higmanVCPivotAC_U_mul_S {d : ℕ} {u s : higmanVCCommon_Q d}
    (hu : u ∈ higmanVCTreeNF_U d) (hs : s ∈ higmanVCTreeNFWitPivot_S d) :
    u * s ∈ higmanVCTreeNFWitPivot_S d := by
  obtain ⟨u₁, hu₁, C, hC, h, hh, u₂, hu₂, rfl⟩ := higmanVCTreeNFWitPivot_mem_S.mp hs
  exact higmanVCTreeNFWitPivot_mem_S.mpr
    ⟨u * u₁, (higmanVCTreeNF_U d).mul_mem hu hu₁, C, hC, h, hh, u₂, hu₂, by simp only [mul_assoc]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_U_mul_S

/-- **The reduction.**  Deep closure at any depth `L` gives antichain pivot closure. -/
theorem higmanVCPivotAC_ACClosed_of_Closed {d L : ℕ} (hd : 1 < d) {t : higmanVCCommon_Q d}
    (ht : higmanVCPivotAC_Closed d L t) : higmanVCTreeNFWitPivot_ACClosed d t := by
  intro C hC h hh u hu
  obtain ⟨g, rfl⟩ := higmanVCTreeNF_mk_surjective d u
  obtain ⟨N, hN⟩ := higmanVCCommon_push hd g⁻¹
  have hC' := higmanVCPivotAC_refine_isAC hC (L + N)
  have hh' := higmanVCPivotAC_H_le_refine hC (L + N) hh
  have hlen : ∀ c ∈ higmanVCPivotAC_refine C (L + N), L + N ≤ c.length :=
    fun _ hc => higmanVCPivotAC_refine_length hc
  have hconj := higmanVCPivotAC_conj_mem (B := L) hd hN hC' hlen hh'
  have hS := ht _ (higmanVCPivotAC_push_isAC (B := L) hd g⁻¹ hC')
    (fun _ hx => higmanVCPivotAC_push_length hd hx) _ hconj
  have e : h * higmanVCCommon_mk d g * t = higmanVCCommon_mk d g *
      (higmanVCCommon_mk d g⁻¹ * h * (higmanVCCommon_mk d g⁻¹)⁻¹ * t) := by
    rw [map_inv, inv_inv]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [e]
  exact higmanVCPivotAC_U_mul_S hu hS

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_ACClosed_of_Closed

/-- Antichain pivot closure gives deep closure at every depth (take `u = 1`). -/
theorem higmanVCPivotAC_Closed_of_ACClosed {d L : ℕ} {t : higmanVCCommon_Q d}
    (ht : higmanVCTreeNFWitPivot_ACClosed d t) : higmanVCPivotAC_Closed d L t := by
  intro C hC _ h hh
  have h1 := ht C hC h hh 1 (higmanVCTreeNF_U d).one_mem
  rwa [mul_one] at h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_Closed_of_ACClosed

/-- **Endpoint**: Y gives X. -/
theorem higmanVCPivotAC_X_of_Y (h : HigmanVCPivotACStatement) :
    HigmanVCTreeNFWitPivotStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, ht⟩ := h d hd N
  exact ⟨n, hn, a, b, ha, hb, hab, hba, higmanVCPivotAC_ACClosed_of_Closed hd ht⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_X_of_Y

/-- **LOUD**: X gives Y, so Y is equivalent to X as a Prop. -/
theorem higmanVCPivotAC_Y_of_X (h : HigmanVCTreeNFWitPivotStatement) :
    HigmanVCPivotACStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, ht⟩ := h d hd N
  exact ⟨n, hn, a, b, ha, hb, hab, hba, higmanVCPivotAC_Closed_of_ACClosed ht⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_Y_of_X

/-- **Endpoint**: Y gives the witness Statement. -/
theorem higmanVCPivotAC_wit_of_Y (h : HigmanVCPivotACStatement) :
    HigmanVCTreeNFWitStatement :=
  higmanVCTreeNFWitPivot_wit_of_X (higmanVCPivotAC_X_of_Y h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_wit_of_Y

/-- **Endpoint**: Y gives (1) at every `d > 1`. -/
theorem higmanVCPivotAC_ker_le_of_Y (h : HigmanVCPivotACStatement) (d : ℕ) (hd : 1 < d) :
    (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) :=
  higmanVCTreeNFWitPivot_ker_le_of_X (higmanVCPivotAC_X_of_Y h) d hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_ker_le_of_Y

end GroupApproximation.BooneHigman.Metabelian.Envelope
