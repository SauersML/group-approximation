import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCStepBCore
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Step B core: the one-antichain case and a normalised residual (lane bh-met-93r)

Notation as in `EnvelopeHigmanVCStepBCore`: `Q = higmanVCCommon_Q d`, `U = higmanVCTreeNF_U d`,
`H_A = higmanVCTreeNFWitPivot_H d A`, `S = U · ⋃_A H_A · U`.

**Proved here (unconditional).**
* `higmanVCStepBCore_mem_S_of_oneAC`: the *one-antichain case*.  If there are an antichain
  `A` and `u, v ∈ U` with `u h ∈ H_A` and `P v ∈ H_A`, then
  `h P = u⁻¹ · (u h)(P v) · v⁻¹ ∈ U H_A U = S`.  This single case contains every case that
  `higmanVCStepB_core_full` discharges: `h ∈ U` (take `A = D`, `u = h⁻¹`), `P ∈ U`
  (take `A = C`, `v = P⁻¹`) and the symmetric case `D ⊆ C ⋆ T` (take `A = C ⋆ T`).
* `higmanVCStepBCore_split_of_core`: the old residual `HigmanVCStepBCoreStatement` implies the
  new residual `HigmanVCStepBCore_SplitStatement` (every instance of the new one is an
  instance of the old one).
* `higmanVCStepBCore_full`: the new residual, extended to every `D` (not necessarily complete)
  and every involution `P`, with the one-antichain case discharged.  `D` is completed at a depth
  `M > L`; the fill words have length `M`, so they still refine `C` and stay deeper than `C`.

**The residual `HigmanVCStepBCore_SplitStatement` (NOT proved; LOUD).**  Compared with
`HigmanVCStepBCoreStatement` it assumes in addition that `D` is a *complete* code and that
`P * P = 1`, and it replaces the three exclusions (`h ∉ U`, `P ∉ U`, `D` not symmetric) by the
single, stronger exclusion "not the one-antichain case".  So its instance set is strictly
smaller.  **As a `Prop` it is EQUIVALENT to the old residual and to Higman (1)**: it follows
from the old residual (proved here), it implies letter-closure of `S` and Higman (1)
(`EnvelopeHigmanVCStepBCoreSplitWire`), and Higman (1) gives `Q = S`, hence both residuals.
The progress is in proof content only: fewer, more normalised instances.

Truth check (python, `SP/bh-met-93r/split_check.py`, assuming `Q ≅ V_d` and Claim F):
sampled `C` complete, `D` complete and strictly deeper, non-symmetric, `P` an involution;
see the lane report for the counts.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The one-antichain case: `u h ∈ H_A` and `P v ∈ H_A` for an antichain `A` and `u, v ∈ U`. -/
def higmanVCStepBCore_OneAC (d : ℕ) (h P : higmanVCCommon_Q d) : Prop :=
  ∃ A : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC A ∧ ∃ u ∈ higmanVCTreeNF_U d,
    ∃ v ∈ higmanVCTreeNF_U d, u * h ∈ higmanVCTreeNFWitPivot_H d A ∧
      P * v ∈ higmanVCTreeNFWitPivot_H d A

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepBCore_OneAC

/-- The one-antichain case lies in `S`. -/
theorem higmanVCStepBCore_mem_S_of_oneAC {d : ℕ} {h P : higmanVCCommon_Q d}
    (hA : higmanVCStepBCore_OneAC d h P) : h * P ∈ higmanVCTreeNFWitPivot_S d := by
  obtain ⟨A, hAC, u, hu, v, hv, h1, h2⟩ := hA
  refine higmanVCTreeNFWitPivot_mem_S.mpr ⟨u⁻¹, (higmanVCTreeNF_U d).inv_mem hu, A, hAC,
    u * h * (P * v), (higmanVCTreeNFWitPivot_H d A).mul_mem h1 h2, v⁻¹,
    (higmanVCTreeNF_U d).inv_mem hv, ?_⟩
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepBCore_mem_S_of_oneAC

/-- **Normalised core residual (NOT proved).**  `C` a complete code, `D` a complete code that
refines `C` and is strictly deeper, `h ∈ H_C`, `P ∈ H_D` an involution, and `(h, P)` not in the
one-antichain case.  Then `h · P ∈ S`. -/
def HigmanVCStepBCore_SplitStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C →
    (∃ L : ℕ, (∀ c ∈ C, c.length ≤ L) ∧ ∀ w : List (Fin d), w.length = L → ∃ c ∈ C, c <+: w) →
    ∀ D : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC D →
    (∃ M : ℕ, (∀ z ∈ D, z.length ≤ M) ∧ ∀ w : List (Fin d), w.length = M → ∃ z ∈ D, z <+: w) →
    (∀ z ∈ D, ∃ c ∈ C, c <+: z) → (∀ z ∈ D, ∀ c ∈ C, c.length < z.length) →
    ∀ h ∈ higmanVCTreeNFWitPivot_H d C, ∀ P ∈ higmanVCTreeNFWitPivot_H d D, P * P = 1 →
    ¬ higmanVCStepBCore_OneAC d h P →
    h * P ∈ higmanVCTreeNFWitPivot_S d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCStepBCore_SplitStatement

/-- The old core residual implies the normalised one. -/
theorem higmanVCStepBCore_split_of_core (hK : HigmanVCStepBCoreStatement) :
    HigmanVCStepBCore_SplitStatement := by
  intro d hd C hC hCL D hD _ href hdeep h hh P hP _ hne
  refine hK d hd C hC hCL D hD href hdeep ?_ h hh ?_ P hP ?_
  · intro T hT hsub
    refine hne ⟨higmanVCLeafExp_star C T,
      higmanVCLeafExp_star_isAC hC (higmanVCLeafExp_tree_isAC hT), 1,
      (higmanVCTreeNF_U d).one_mem, 1, (higmanVCTreeNF_U d).one_mem, ?_, ?_⟩
    · rw [one_mul]
      exact higmanVCLeafExp_H_le_star hC hT hh
    · rw [mul_one]
      exact higmanVCPivotY_H_mono hsub hP
  · intro hU
    refine hne ⟨D, hD, h⁻¹, (higmanVCTreeNF_U d).inv_mem hU, 1, (higmanVCTreeNF_U d).one_mem,
      ?_, ?_⟩
    · rw [inv_mul_cancel]
      exact (higmanVCTreeNFWitPivot_H d D).one_mem
    · rw [mul_one]
      exact hP
  · intro hPU
    refine hne ⟨C, hC, 1, (higmanVCTreeNF_U d).one_mem, P⁻¹, (higmanVCTreeNF_U d).inv_mem hPU,
      ?_, ?_⟩
    · rw [one_mul]
      exact hh
    · rw [mul_inv_cancel]
      exact (higmanVCTreeNFWitPivot_H d C).one_mem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepBCore_split_of_core

end GroupApproximation.BooneHigman.Metabelian.Envelope
