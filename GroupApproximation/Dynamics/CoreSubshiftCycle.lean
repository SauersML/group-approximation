import GroupApproximation.Dynamics.RetainedSubshiftPeriodic
import GroupApproximation.Dynamics.CoreSubshift
import GroupApproximation.Meta.AxiomGuard

/-!
# The symbolic core is nonempty and satisfies the cycle condition

`non_mf_groups_exist.tex`, proof of `lem:chain-core-models` (tex 1406–1411):

> It is nonempty, and `Z_{r+1} ⊆ Z_r`, since a higher-level cycle projects to a closed walk at a
> lower level.  Put `Y_0 = ⋂_r Z_r`.  Compactness makes `Y_0` nonempty, and all its words belong
> to `X`, so `Y_0 ⊆ X`.  At each fixed length the decreasing finite languages of `Z_r` stabilize to
> the language of `Y_0`.  Consequently `Y_0` satisfies the cycle condition too.

* `coreSubshift_nonempty`: `Y_0` is nonempty, by compactness;
* `cycleCondition_coreSubshift`: `Y_0` satisfies the cycle condition; at the length of the tested
  edges the languages of `Z_r` and `Y_0` agree for large `r`, and `Z_r` satisfies the cycle
  condition (`cycleCondition_retainedSubshift`).
-/

namespace GroupApproximation.ChainCore

open Set SymbolicDynamics.FullShift GroupApproximation.WordGraph

/-- **`Y_0` is nonempty** (tex 1408–1409): the retained subshifts are nonempty, closed and
decreasing in the compact space `A^ℤ`. -/
theorem coreSubshift_nonempty {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    {X : Set (ℤ → A)} (hX : ∀ n : ℤ, MapsTo (shift n) X X) (hne : X.Nonempty) :
    (coreSubshift X).Nonempty :=
  nonempty_iInter_of_antitone (retainedSubshift_antitone X) (isClosed_retainedSubshift X)
    (retainedSubshift_nonempty hX hne)

/-- **`Y_0` satisfies the cycle condition** (tex 1410–1411). -/
theorem cycleCondition_coreSubshift {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    [Finite A] {X : Set (ℤ → A)} (_hXc : IsClosed X) (_hX : ∀ n : ℤ, Set.MapsTo (shift n) X X) :
    CycleCondition (coreSubshift X) := by
  intro s w hw
  obtain ⟨R, hR⟩ := exists_language_retainedSubshift_eq X (s + 1)
  have hL := hR R le_rfl
  have hedge : wordEdge (retainedSubshift X R) s = wordEdge (coreSubshift X) s := by
    funext u v
    unfold wordEdge
    rw [hL]
  have hcyc := cycleCondition_retainedSubshift X R s w (by rw [hL]; exact hw)
  refine ⟨hw, ?_⟩
  rw [← hedge]
  exact hcyc.2

end GroupApproximation.ChainCore

#audit_axioms GroupApproximation.ChainCore.coreSubshift_nonempty
#audit_axioms GroupApproximation.ChainCore.cycleCondition_coreSubshift
