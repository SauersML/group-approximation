import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCStepBClosed
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCPivotYComplete
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCLeafExpTree
import GroupApproximation.Meta.AxiomGuard

/-!
# Step B, part 2: the combinatorial core residual (lane bh-met-93f)

Notation as in `EnvelopeHigmanVCStepBClosed`.  For antichains `C` and `D`, `H_C · H_D` is a
product of two antichain subgroups.

**The residual `HigmanVCStepBCoreStatement` (NOT proved; LOUD).**  Suppose:
* `C` is a complete prefix code: an antichain, bounded by some `L`, covering every word of
  length `L`;
* `D` is an antichain that refines `C` and is strictly deeper than every word of `C`;
* `D` is *not symmetric*, meaning `D ⊄ C ⋆ T` for every tree `T`;
* `h ∈ H_C \ U` and `P ∈ H_D \ U`.

Then `h · P ∈ S`.  The statement mentions no `E`, no `ker E`, no centrality and no `V_d`.
It is a pure statement about products of antichain subgroups inside `Q`.

**Cases discharged here** (`higmanVCStepB_core_full`):
* `h ∈ U`: `U · S ⊆ S`.
* `P ∈ U`: `S · U ⊆ S`.
* `D ⊆ C ⋆ T` for a tree `T`: pattern refinement puts `h` in `H_{C⋆T}`, so `h · P` lies in
  the single antichain subgroup `H_{C⋆T}`.

The remaining case is exactly the residual.  `EnvelopeHigmanVCStepBReduce` then derives
letter-closure of `S` from it, and hence Higman (1).  That file discharges, by proved
lemmas and with no `E`:
* comparable letters, which are trivial in `Q`;
* the right balanced factor `u₂ = mk g`, pushed through by `higmanVCPivotAC_conj_mem`;
* the depth of the letter's antichain, via `higmanVCPivotAC_refine`;
* the completion of `C` to a complete code, via `higmanVCPivotY_complete`.

**Status, stated honestly.**
* As a `Prop`, the residual is Higman-strength: it implies (1) (proved here), and it follows
  from `Q = S`.
* Relative to the lane target `higmanVCStepB_Closed`, it is strictly smaller in proof
  content, because every case above is removed.
* It is **not** claimed to be smaller than the existing `Y`/`W⁷` residuals.  Its left factor
  `h` is an arbitrary element of `H_C \ U`, not a single letter.
* It is not a restatement of the `W''⇔…⇔W⁷` chain.  It needs no `E`-lift and no central
  element.

Truth check (python, `SP/bh-met-93f/core_check.py`, d = 2, 3): assume `Q ≅ V_d` and use
Claim F.  Every sampled instance has a tree pair with equal length multisets, i.e. lies in
`E(S)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Core residual (NOT proved).**  Products `h · P` with `h ∈ H_C \ U`, `P ∈ H_D \ U`,
where `C` is a complete code and `D` is a strictly deeper, non-symmetric refinement of it,
lie in `S`. -/
def HigmanVCStepBCoreStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C →
    (∃ L : ℕ, (∀ c ∈ C, c.length ≤ L) ∧ ∀ w : List (Fin d), w.length = L → ∃ c ∈ C, c <+: w) →
    ∀ D : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC D →
    (∀ z ∈ D, ∃ c ∈ C, c <+: z) → (∀ z ∈ D, ∀ c ∈ C, c.length < z.length) →
    (∀ T : Finset (List (Fin d)), higmanVCLeafExp_IsTree T → ¬ D ⊆ higmanVCLeafExp_star C T) →
    ∀ h ∈ higmanVCTreeNFWitPivot_H d C, h ∉ higmanVCTreeNF_U d →
    ∀ P ∈ higmanVCTreeNFWitPivot_H d D, P ∉ higmanVCTreeNF_U d →
    h * P ∈ higmanVCTreeNFWitPivot_S d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCStepBCoreStatement

/-- Two incomparable words form an antichain. -/
theorem higmanVCStepB_pair_isAC {d : ℕ} {x y : List (Fin d)} (h1 : ¬ x <+: y)
    (h2 : ¬ y <+: x) : higmanVCTreeNFWitPivot_IsAC ({x, y} : Finset (List (Fin d))) := by
  intro u hu v hv huv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
    first | exact absurd rfl huv | assumption

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepB_pair_isAC

/-- An antichain subgroup lies in `S`. -/
theorem higmanVCStepB_H_mem_S {d : ℕ} {D : Finset (List (Fin d))}
    (hD : higmanVCTreeNFWitPivot_IsAC D) {P : higmanVCCommon_Q d}
    (hP : P ∈ higmanVCTreeNFWitPivot_H d D) : P ∈ higmanVCTreeNFWitPivot_S d :=
  higmanVCTreeNFWitPivot_mem_S.mpr ⟨1, (higmanVCTreeNF_U d).one_mem, D, hD, P, hP, 1,
    (higmanVCTreeNF_U d).one_mem, by rw [one_mul, mul_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepB_H_mem_S

/-- The residual, extended to all cases.  The balanced cases (`h ∈ U` or `P ∈ U`) and the
symmetric case (`D ⊆ C ⋆ T`) are proved here.  Only the remaining case uses `hK`. -/
theorem higmanVCStepB_core_full (hK : HigmanVCStepBCoreStatement) {d : ℕ} (hd : 1 < d)
    {C : Finset (List (Fin d))} (hC : higmanVCTreeNFWitPivot_IsAC C)
    (hCL : ∃ L : ℕ, (∀ c ∈ C, c.length ≤ L) ∧
      ∀ w : List (Fin d), w.length = L → ∃ c ∈ C, c <+: w)
    {D : Finset (List (Fin d))} (hD : higmanVCTreeNFWitPivot_IsAC D)
    (href : ∀ z ∈ D, ∃ c ∈ C, c <+: z) (hdeep : ∀ z ∈ D, ∀ c ∈ C, c.length < z.length)
    {h : higmanVCCommon_Q d} (hh : h ∈ higmanVCTreeNFWitPivot_H d C)
    {P : higmanVCCommon_Q d} (hP : P ∈ higmanVCTreeNFWitPivot_H d D) :
    h * P ∈ higmanVCTreeNFWitPivot_S d := by
  by_cases hU : h ∈ higmanVCTreeNF_U d
  · exact higmanVCPivotAC_U_mul_S hU (higmanVCStepB_H_mem_S hD hP)
  by_cases hPU : P ∈ higmanVCTreeNF_U d
  · exact higmanVCTreeNFWitPivot_S_mul_U (higmanVCStepB_H_mem_S hC hh) hPU
  by_cases hsym : ∃ T : Finset (List (Fin d)),
      higmanVCLeafExp_IsTree T ∧ D ⊆ higmanVCLeafExp_star C T
  · obtain ⟨T, hT, hsub⟩ := hsym
    exact higmanVCStepB_H_mem_S (higmanVCLeafExp_star_isAC hC (higmanVCLeafExp_tree_isAC hT))
      (Subgroup.mul_mem _ (higmanVCLeafExp_H_le_star hC hT hh)
        (higmanVCPivotY_H_mono hsub hP))
  · exact hK d hd C hC hCL D hD href hdeep (fun T hT hsub => hsym ⟨T, hT, hsub⟩)
      h hh hU P hP hPU

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepB_core_full

end GroupApproximation.BooneHigman.Metabelian.Envelope
