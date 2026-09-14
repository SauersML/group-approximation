import GroupApproximation.Dynamics.ChainRecurrence
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Separation.Profinite
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:transient-matrices`: the transient part has no periodic points

`non_mf_groups_exist.tex`, the proof of Lemma `lem:transient-matrices` (tex 1485–1487 at origin/main
`68481e4d7`):

> Put $U=X\setminus Y$.  A compact subset $C\subset U$ has a finite cover by wandering clopen sets,
> say $m$ of them, so each orbit meets $C$ in at most $m$ points.  Also $U$ has no periodic points.

`Y = CR(T)`.  A periodic point is chain recurrent: its own orbit segment is an exact chain back to
itself, and every step lies on the diagonal, which every entourage contains.
-/

namespace GroupApproximation.Dynamics

variable {X : Type*} [UniformSpace X]

/-- **Periodic points are chain recurrent**: if `T^[n] x = x` with `n ≥ 1`, the orbit segment
`x, T x, …, T^[n] x = x` is a chain of positive length whose steps are exact. -/
theorem isChainRecurrent_of_isPeriodicPt {T : X → X} {n : ℕ} {x : X} (hn : 0 < n)
    (hx : Function.IsPeriodicPt T n x) : IsChainRecurrent T x := by
  intro V hV
  rw [transGen_iff_exists_seq]
  refine ⟨n, by omega, fun i => T^[i] x, rfl, hx, fun i _ => ?_⟩
  show (T (T^[i] x), T^[i + 1] x) ∈ V
  have h : T^[i + 1] x = T (T^[i] x) := Function.iterate_succ_apply' (f := T) i x
  rw [h]
  exact refl_mem_uniformity hV

/-- **Printed (tex 1487).**  "Also $U$ has no periodic points", for `U = X ∖ CR(T)`: no point
outside the chain-recurrent set satisfies `T^[n] x = x` with `n ≥ 1`. -/
def PrintedTransientNoPeriodicPoints : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (x : X), x ∉ chainRecurrentSet ⇑T → ∀ n : ℕ, 0 < n → ¬ Function.IsPeriodicPt ⇑T n x

theorem printedTransientNoPeriodicPoints : PrintedTransientNoPeriodicPoints :=
  fun _ _ _ _ _ _ hx _ hn hper => hx (isChainRecurrent_of_isPeriodicPt hn hper)

end GroupApproximation.Dynamics

#audit_axioms GroupApproximation.Dynamics.isChainRecurrent_of_isPeriodicPt
#audit_closed_axioms GroupApproximation.Dynamics.printedTransientNoPeriodicPoints
