import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitOneKer
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCAllReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFConverse
import GroupApproximation.Meta.AxiomGuard

/-!
# Step B, part 1: right-closure of `S` under letters closes Higman (1) (lane bh-met-93f)

Notation: `Q = higmanVCCommon_Q d`, `mk = higmanVCCommon_mk d`, `U = higmanVCTreeNF_U d`,
`H_C = higmanVCTreeNFWitPivot_H d C`, and `S = U · ⋃_{C antichain} H_C · U`
(`higmanVCTreeNFWitPivot_S d`).

**Proved here (unconditional, no Higman input, and `E` is never used to build elements).**
* `higmanVCStepB_Closed d`: `S` is closed under right multiplication by every generator
  `mk (of (x, y))` of `Q`.
* `higmanVCStepB_mul_mem`: `Closed d` gives `S · mk g ⊆ S` for every word `g`.  The proof
  is by induction on `g`.  Letters are involutions in `Q`, so the inverse case is the
  letter case.
* `higmanVCStepB_mem_S_of_closed`: `Closed d` gives `Q = S`, since `1 ∈ S` and `mk` is
  onto.
* `higmanVCStepB_ker_le_of_closed`: `Closed d` gives `ker (evalAll) ≤ normalClosure rels`.
  If `evalAll r = 1`, then `mk r ∈ S ∩ ker E`.  By lane 92y
  (`higmanVCOrbitOne_eq_one_of_mem_S`) this forces `mk r = 1`.
* `higmanVCStepB_antichain_of_closed`: `(∀ d > 1, Closed d)` gives
  `HigmanVCAllAntichainStatement`, via `higmanVCAll_antichain_of_ker_le`.

`E` enters only through the proved lemma `S ∩ ker E = 1`.  It is never used to produce an
element of `Q`.  No central element is lifted or killed.

**LOUD: `Closed d` is NOT proved in this file.**  `EnvelopeHigmanVCStepBCore` reduces it to
one combinatorial residual, `HigmanVCStepBCoreStatement`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `S` is closed under right multiplication by every letter `mk (of (x, y))` of `Q`. -/
def higmanVCStepB_Closed (d : ℕ) : Prop :=
  ∀ s ∈ higmanVCTreeNFWitPivot_S d, ∀ x y : List (Fin d),
    s * higmanVCCommon_mk d (FreeGroup.of (x, y)) ∈ higmanVCTreeNFWitPivot_S d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepB_Closed

/-- Letter-closure of `S` gives closure under right multiplication by every `mk g`. -/
theorem higmanVCStepB_mul_mem {d : ℕ} (hS : higmanVCStepB_Closed d)
    (g : FreeGroup (List (Fin d) × List (Fin d))) :
    ∀ s ∈ higmanVCTreeNFWitPivot_S d,
      s * higmanVCCommon_mk d g ∈ higmanVCTreeNFWitPivot_S d := by
  induction g using FreeGroup.induction_on with
  | C1 =>
    intro s hs
    rw [map_one, mul_one]
    exact hs
  | of p =>
    obtain ⟨x, y⟩ := p
    intro s hs
    exact hS s hs x y
  | inv_of p _ =>
    obtain ⟨x, y⟩ := p
    intro s hs
    rw [higmanVCCommon_mk_inv_of]
    exact hS s hs x y
  | mul g₁ g₂ ih₁ ih₂ =>
    intro s hs
    rw [map_mul, ← mul_assoc]
    exact ih₂ _ (ih₁ s hs)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepB_mul_mem

/-- Letter-closure of `S` gives `S = Q`. -/
theorem higmanVCStepB_mem_S_of_closed {d : ℕ} (hS : higmanVCStepB_Closed d)
    (q : higmanVCCommon_Q d) : q ∈ higmanVCTreeNFWitPivot_S d := by
  obtain ⟨g, rfl⟩ := higmanVCTreeNF_mk_surjective d q
  have key := higmanVCStepB_mul_mem hS g 1 (higmanVCTreeNFWitPivot_one_mem_S d)
  rwa [one_mul] at key

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepB_mem_S_of_closed

/-- Letter-closure of `S` gives Higman's kernel inclusion at arity `d`.  It uses only the
proved fact `S ∩ ker E = 1` (lane 92y). -/
theorem higmanVCStepB_ker_le_of_closed {d : ℕ} (hd : 1 < d) (hS : higmanVCStepB_Closed d) :
    (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) := by
  intro r hr
  refine higmanVCCommon_mk_eq_one_iff.mp ?_
  refine higmanVCOrbitOne_eq_one_of_mem_S hd (higmanVCStepB_mem_S_of_closed hS _) ?_
  rw [higmanVCTreeNF_E_mk]
  exact MonoidHom.mem_ker.mp hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepB_ker_le_of_closed

/-- Endpoint: letter-closure of `S` for all `d > 1` gives `HigmanVCAllAntichainStatement`. -/
theorem higmanVCStepB_antichain_of_closed (h : ∀ d : ℕ, 1 < d → higmanVCStepB_Closed d) :
    HigmanVCAllAntichainStatement :=
  higmanVCAll_antichain_of_ker_le fun d hd => higmanVCStepB_ker_le_of_closed hd (h d hd)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepB_antichain_of_closed

end GroupApproximation.BooneHigman.Metabelian.Envelope
