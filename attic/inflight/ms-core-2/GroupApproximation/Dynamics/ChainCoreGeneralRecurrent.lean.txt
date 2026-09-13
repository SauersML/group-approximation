import GroupApproximation.Dynamics.ChainCoreGeneralFactor
import GroupApproximation.Dynamics.CoreSubshiftChainRecurrent
import GroupApproximation.Dynamics.RefiningClopenPartitions
import GroupApproximation.Meta.AxiomGuard

/-!
# The general core is the chain-recurrent set

`non_mf_groups_exist.tex`, proof of Lemma `lem:chain-core-models` (tex lines 1447–1454):

> Chain recurrence passes to factors, so $Y\subseteq Y_*$.  Conversely, if $x\in Y_*$, choose
> $\mathcal P_m$ with mesh below $\varepsilon$.  A sufficiently accurate closed chain at $\pi_m(x)$ makes
> the zero-coordinate symbol of each next point equal the one-coordinate symbol of the preceding point.
> Lift the intermediate points arbitrarily to $X$, with both endpoint lifts equal to $x$.  Consecutive
> lifts satisfy the $\varepsilon$-chain condition because they lie in the same partition atom after
> shifting.  Hence $Y_*=Y$.

Each atom set `S m` carries the discrete uniformity with its own topology (`discreteQuotientUniformSpace`,
through `UniformSpace.replaceTopology`), so the itinerary subshift is a subshift in the sense of
chain-subshift's `CoreSubshiftChainRecurrent`, whose `Y_0 = CR(T)` is used at each level.

* `chainRecurrentSet_subset_generalCore`: `Y ⊆ Y_*`, by `mapsTo_chainRecurrentSet` along `π_m`.
* `generalCore_subset_chainRecurrentSet`: `Y_* ⊆ Y`, by lifting a closed chain accurate at coordinate zero.
* `generalCore_eq_chainRecurrentSet`: `Y_* = Y`.

## Manuscript status

Infrastructure for `lem:chain-core-models` (tex 1447–1454); certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace ChainCore

open Set SymbolicDynamics.FullShift GroupApproximation.WordGraph GroupApproximation.Dynamics
open scoped Uniformity

section Uniformity

variable {X : Type*} [TopologicalSpace X]

theorem topology_eq_bot_uniformSpace_toTopologicalSpace (S' : DiscreteQuotient X) :
    (inferInstance : TopologicalSpace S') = (⊥ : UniformSpace S').toTopologicalSpace :=
  DiscreteTopology.eq_bot.trans
    (@DiscreteTopology.eq_bot S' (⊥ : UniformSpace S').toTopologicalSpace _).symm

/-- The discrete uniformity on the atoms of a partition, with the quotient topology. -/
abbrev discreteQuotientUniformSpace (S' : DiscreteQuotient X) : UniformSpace S' :=
  (⊥ : UniformSpace S').replaceTopology (topology_eq_bot_uniformSpace_toTopologicalSpace S')

end Uniformity

attribute [local instance] discreteQuotientUniformSpace

variable {X : Type*} [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X) {S : ℕ → DiscreteQuotient X}

/-- **`Y ⊆ Y_*`**: chain recurrence passes to the itinerary factors, whose chain-recurrent points are
the symbolic cores. -/
theorem chainRecurrentSet_subset_generalCore : chainRecurrentSet T ⊆ generalCore T S := by
  intro x hx
  refine (mem_inverseLimitCore T).2 fun m ↦ ?_
  have hX := mapsTo_shift_itinerarySubshift T (S m)
  let π : X → itinerarySubshift T (S m) := fun y ↦ ⟨itinerary T (S m) y, y, rfl⟩
  have hπ : Continuous π := (continuous_itinerary T (S m)).subtype_mk _
  have hsemi : Function.Semiconj π T
      ((hX 1).restrict (shift 1) (itinerarySubshift T (S m)) (itinerarySubshift T (S m))) :=
    fun y ↦ Subtype.ext (itinerary_apply_self T (S m) y)
  exact (isChainRecurrent_iff_mem_coreSubshift hX (π x)).1 (mapsTo_chainRecurrentSet hπ hsemi hx)

/-- **`Y_* ⊆ Y`**: a closed chain at `π_m(x)` accurate at coordinate zero lifts to a closed
`ε`-chain at `x`, once the atoms of `S m` have diameter below `ε`. -/
theorem generalCore_subset_chainRecurrentSet (hS : IsRefiningClopenPartitions S) :
    generalCore T S ⊆ chainRecurrentSet T := by
  intro x hx V hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.1 hV
  obtain ⟨m, hm⟩ := hS.mesh_lt ε hε
  have hX := mapsTo_shift_itinerarySubshift T (S m)
  let π : X → itinerarySubshift T (S m) := fun y ↦ ⟨itinerary T (S m) y, y, rfl⟩
  have step : ∀ (a b : X) (c w : itinerarySubshift T (S m)), π a = c → π b = w →
      ChainStep ((hX 1).restrict (shift 1) (itinerarySubshift T (S m)) (itinerarySubshift T (S m)))
        (windowRel (itinerarySubshift T (S m)) 0) c w → ChainStep T V a b := by
    intro a b c w ha hb hcw
    subst ha hb
    rw [chainStep_windowRel_iff hX] at hcw
    have h0 := hcw 0 (by simp)
    change itinerary T (S m) a (1 + 0) = itinerary T (S m) b 0 at h0
    rw [add_zero, itinerary_apply, zpow_one, itinerary_apply_zero] at h0
    exact hεV (hm _ _ h0)
  have key : ∀ z w : itinerarySubshift T (S m),
      Relation.TransGen
        (ChainStep ((hX 1).restrict (shift 1) (itinerarySubshift T (S m))
          (itinerarySubshift T (S m))) (windowRel (itinerarySubshift T (S m)) 0)) z w →
      ∀ a b : X, π a = z → π b = w → Relation.TransGen (ChainStep T V) a b := by
    intro z w h
    induction h with
    | single hzw =>
      intro a b ha hb
      exact Relation.TransGen.single (step a b _ _ ha hb hzw)
    | @tail c w _ hcw ih =>
      intro a b ha hb
      obtain ⟨c', hc'⟩ := c.2
      have hπc : π c' = c := Subtype.ext hc'
      exact (ih a c' ha hπc).tail (step c' b c w hπc hb hcw)
  have hcore : IsChainRecurrent
      ((hX 1).restrict (shift 1) (itinerarySubshift T (S m)) (itinerarySubshift T (S m))) (π x) :=
    (isChainRecurrent_iff_mem_coreSubshift hX (π x)).2 ((mem_inverseLimitCore T).1 hx m)
  exact key _ _ (hcore _ (windowRel_mem_uniformity _ 0)) x x rfl rfl

/-- **`Y_* = Y`** (tex 1454). -/
theorem generalCore_eq_chainRecurrentSet (hS : IsRefiningClopenPartitions S) :
    generalCore T S = chainRecurrentSet T :=
  (generalCore_subset_chainRecurrentSet T hS).antisymm (chainRecurrentSet_subset_generalCore T)

end ChainCore
end GroupApproximation

#audit_axioms GroupApproximation.ChainCore.chainRecurrentSet_subset_generalCore
#audit_axioms GroupApproximation.ChainCore.generalCore_subset_chainRecurrentSet
#audit_axioms GroupApproximation.ChainCore.generalCore_eq_chainRecurrentSet
