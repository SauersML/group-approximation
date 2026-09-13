import GroupApproximation.Dynamics.FirstReturnMap
import GroupApproximation.Dynamics.ChainRecurrence
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:dynamic-rank-budget`: the induced core lies in the core

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1743–1750:

> The induced core is $C\cap Y$.  Indeed its return ring is a corner
> of the LEF ring $R_Y$, so it lies in the induced chain-recurrent core.
> Conversely, saturating that core through the finite towers gives a
> closed invariant subsystem whose ring is a corner of a matrix ring
> over an LEF ring, hence LEF.  Theorem~\ref{thm:core-ring-reflection}
> applied to this subsystem makes every one of its points chain recurrent
> in $X$, proving the reverse inclusion.  The return transient ideal
> is therefore $J=p_CIp_C$.

The later steps of the proof use one inclusion, `CR(S_C) ⊆ C ∩ Y`: a point of the return section
that is chain recurrent for the first-return map `S_C` is chain recurrent for `T`.  It is proved
here as `coe_mem_chainRecurrentSet_of_firstReturn`.

Route.  The printed proof of this inclusion saturates the induced core through the towers and
applies Theorem `thm:core-ring-reflection` to the saturated subsystem.  This module uses a shorter
direct argument instead: one step of `S_C` is `h ≥ 1` exact steps of `T` followed by the same
close step, so every `S_C`-chain is a `T`-chain for the same entourage.  The census records these
sentences as `partial` for that reason; the printed saturation route and the reverse inclusion
`C ∩ Y ⊆ CR(S_C)` remain to be formalized.

* `transGen_chainStep_of_zpow`: `m + 1` exact steps of `T` followed by a `V`-close step form a
  `V`-chain.
* `transGen_of_firstReturn_step`: one `S_C`-step for the entourage induced on `C` is a `T`-chain.
* `coe_mem_chainRecurrentSet_of_firstReturn`: `CR(S_C) ⊆ C ∩ CR(T)`.
-/

namespace GroupApproximation.ChainCore.DynamicRankBudget

open Topology Uniformity

variable {X : Type*} [UniformSpace X] {T : X ≃ₜ X} {r : ℕ} {C : Set X}

/-- `m + 1` exact steps of `T` followed by one `V`-close step form a `V`-chain. -/
theorem transGen_chainStep_of_zpow {V : Set (X × X)} (hV : V ∈ 𝓤 X) :
    ∀ (m : ℕ) (a b : X), ((T ^ ((m + 1 : ℕ) : ℤ)) a, b) ∈ V →
      Relation.TransGen (Dynamics.ChainStep ⇑T V) a b := by
  intro m
  induction m with
  | zero =>
    intro a b h
    refine Relation.TransGen.single ?_
    change (T a, b) ∈ V
    simpa using h
  | succ m ih =>
    intro a b h
    have e : (T ^ ((m + 1 + 1 : ℕ) : ℤ)) a = (T ^ ((m + 1 : ℕ) : ℤ)) (T a) := by
      rw [show ((m + 1 + 1 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) + 1 by push_cast; ring, zpow_add_one,
        Homeomorph.mul_apply]
    rw [e] at h
    exact Relation.TransGen.head
      (show Dynamics.ChainStep ⇑T V a (T a) from refl_mem_uniformity hV) (ih (T a) b h)

/-- **One step of the first-return map is a chain of `T`** for the same entourage. -/
theorem transGen_of_firstReturn_step (hC : IsReturnSection T r C) {V : Set (X × X)}
    (hV : V ∈ 𝓤 X) {a b : C}
    (hab : Dynamics.ChainStep ⇑(firstReturnHomeomorph hC)
      ((fun q : C × C => ((q.1 : X), (q.2 : X))) ⁻¹' V) a b) :
    Relation.TransGen (Dynamics.ChainStep ⇑T V) (a : X) (b : X) := by
  obtain ⟨h0, -⟩ := returnTime_spec hC (a : X)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, returnTime T C (a : X) = m + 1 :=
    ⟨returnTime T C (a : X) - 1, by omega⟩
  refine transGen_chainStep_of_zpow hV m (a : X) (b : X) ?_
  have e : ((firstReturnHomeomorph hC a : C) : X) = (T ^ ((m + 1 : ℕ) : ℤ)) (a : X) := by
    rw [firstReturnHomeomorph_apply, hm]
  change (((firstReturnHomeomorph hC a : C) : X), (b : X)) ∈ V at hab
  rwa [e] at hab

/-- **The induced core lies in the core** (tex 1743–1750, the inclusion `CR(S_C) ⊆ C ∩ Y`): a point
of the return section that is chain recurrent for the first-return map is chain recurrent for `T`. -/
theorem coe_mem_chainRecurrentSet_of_firstReturn (hC : IsReturnSection T r C) {y : C}
    (hy : y ∈ Dynamics.chainRecurrentSet ⇑(firstReturnHomeomorph hC)) :
    (y : X) ∈ Dynamics.chainRecurrentSet ⇑T := by
  refine Dynamics.mem_chainRecurrentSet.2 fun V hV => ?_
  have hW : (fun q : C × C => ((q.1 : X), (q.2 : X))) ⁻¹' V ∈ 𝓤 C := by
    rw [uniformity_subtype]
    exact Filter.preimage_mem_comap hV
  have h := (Dynamics.mem_chainRecurrentSet.1 hy) _ hW
  suffices key : ∀ a b : C,
      Relation.TransGen (Dynamics.ChainStep ⇑(firstReturnHomeomorph hC)
        ((fun q : C × C => ((q.1 : X), (q.2 : X))) ⁻¹' V)) a b →
        Relation.TransGen (Dynamics.ChainStep ⇑T V) (a : X) (b : X) from key y y h
  intro a b hab
  induction hab with
  | single h1 => exact transGen_of_firstReturn_step hC hV h1
  | tail _ h2 ih => exact ih.trans (transGen_of_firstReturn_step hC hV h2)

end GroupApproximation.ChainCore.DynamicRankBudget

/-! ### Audit -/

#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.transGen_chainStep_of_zpow
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.transGen_of_firstReturn_step
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.coe_mem_chainRecurrentSet_of_firstReturn
