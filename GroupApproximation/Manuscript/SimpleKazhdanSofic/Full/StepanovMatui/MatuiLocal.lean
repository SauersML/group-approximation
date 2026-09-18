import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiFragment
import GroupApproximation.Meta.AxiomGuard

namespace GroupApproximation
namespace Full
namespace StepanovMatui
namespace Matui

/-!
# Three-cycles from local pieces

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–309:

> For derived topological full groups, Matui showed by a similar argument that a nontrivial normal
> subgroup meets a simple union of products of alternating groups on towers
> [Matui, Lemma 3.4 and Theorem 4.9].

Part of work order WO-A2.  If every point of the base `U` of a three-cycle datum has a clopen
neighbourhood `W` such that the three-cycles on all clopen `A ⊆ U ∩ W` lie in a subgroup `N`, then
`threeCycle f U ∈ N` (`threeCycle_mem_of_local`).  By compactness finitely many `W` cover `U`, and
`threeCycle_union` splits the three-cycle along `A ∩ W` and `A \ W`.
-/

open scoped commutatorElement

variable {X : Type*}

/-- **Local-to-global for three-cycles.** -/
theorem threeCycle_mem_of_local [TopologicalSpace X] [CompactSpace X]
    {N : Subgroup (Equiv.Perm X)} {f : Equiv.Perm X} {U : Set X} (hU : IsClopen U)
    (h : IsThreeCycleDatum f U)
    (hloc : ∀ x ∈ U, ∃ W : Set X, IsClopen W ∧ x ∈ W ∧
      ∀ A : Set X, IsClopen A → A ⊆ U → A ⊆ W → threeCycle f A ∈ N) :
    threeCycle f U ∈ N := by
  classical
  choose! W hWc hxW hWN using hloc
  obtain ⟨t, htU, hcover⟩ := hU.isClosed.isCompact.elim_nhds_subcover W
    fun x hx => (hWc x hx).isOpen.mem_nhds (hxW x hx)
  have key : ∀ s : Finset X, (∀ x ∈ s, x ∈ U) → ∀ A : Set X, IsClopen A → A ⊆ U →
      A ⊆ ⋃ x ∈ s, W x → threeCycle f A ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ A _ _ hA
      have hA0 : A ⊆ ∅ := fun y hy => by
        obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.mp (hA hy)
        exact absurd hi (Finset.notMem_empty i)
      rw [Set.subset_empty_iff.mp hA0, threeCycle_empty]
      exact N.one_mem
    | insert a s _ ih =>
      intro hsU A hAc hAU hA
      have haU : a ∈ U := hsU a (Finset.mem_insert_self a s)
      have hsU' : ∀ x ∈ s, x ∈ U := fun x hx => hsU x (Finset.mem_insert_of_mem hx)
      have hAU1 : A ∩ W a ⊆ U := fun y hy => hAU hy.1
      have hAU2 : A \ W a ⊆ U := fun y hy => hAU hy.1
      have hW1 : A ∩ W a ⊆ W a := fun y hy => hy.2
      have hW2 : A \ W a ⊆ ⋃ x ∈ s, W x := by
        intro y hy
        have hy' := hA hy.1
        rw [Finset.set_biUnion_insert] at hy'
        exact Or.resolve_left hy' hy.2
      have h1 : threeCycle f (A ∩ W a) ∈ N :=
        hWN a haU (A ∩ W a) (hAc.inter (hWc a haU)) hAU1 hW1
      have h2 : threeCycle f (A \ W a) ∈ N :=
        ih hsU' (A \ W a) (hAc.diff (hWc a haU)) hAU2 hW2
      have hdisj : Disjoint (A ∩ W a) (A \ W a) :=
        Set.disjoint_left.mpr fun y hy1 hy2 => hy2.2 hy1.2
      have e := threeCycle_union h hAU1 hAU2 hdisj
      rw [Set.inter_union_sdiff] at e
      rw [e]
      exact N.mul_mem h1 h2
  exact key t htU U hU Set.Subset.rfl hcover

end Matui
end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.threeCycle_mem_of_local
