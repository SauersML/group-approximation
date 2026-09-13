import GroupApproximation.Dynamics.ChainRecurrence
import Mathlib.Topology.Separation.Profinite
import GroupApproximation.Meta.AxiomGuard

/-!
# The complement of the chain-recurrent set is covered by wandering defects

`non_mf_groups_exist.tex`, `lem:chain-core-models`: "The complement $X\setminus Y$ is covered by
translates of sets $P\setminus T(P)$, where $P$ is clopen and $T(P)\subseteq P$.  Each of these
sets is wandering: its distinct integer translates are pairwise disjoint."

Here `Y = CR(T)` is `chainRecurrentSet T` (`GroupApproximation.Dynamics.ChainRecurrence`).  The
covering is proved directly, by the atom-graph argument, for compact Hausdorff totally
disconnected `X`:

* `exists_clopenPartition_subset`: a finite clopen partition finer than an entourage `V`, as an
  equivalence relation `E ⊆ V` whose classes (the atoms) are open;
* `isClopen_of_saturated`, `image_chainReach_subset`, `apply_mem_chainReach`: the points reached
  from `x` by an `E`-chain of positive length form a clopen `P` with `T(P) ⊆ P` and `Tx ∈ P`.
  `P` is the union of the atoms reached from the atom of `Tx` in the atom graph, where `A → B`
  when `T(A)` meets `B`;
* `exists_isClopen_apply_mem_diff`: if `x` is not chain recurrent, choose `V` with no `V`-chain
  from `x` to `x`.  Then `x ∉ P`, so `Tx ∈ P \ T(P)` and `x` lies in the translate
  `T⁻¹(P \ T(P))`;
* closed endpoint `printedChainCoreCovering`, with wandering from `isWandering_diff_image`.
-/

open scoped Uniformity Topology

namespace GroupApproximation.Dynamics

variable {X : Type*}

/-- A set saturated for an equivalence relation with open classes is clopen. -/
theorem isClopen_of_saturated [TopologicalSpace X] {E : Set (X × X)}
    (hE : ∀ a, IsOpen {b | (a, b) ∈ E}) (hrefl : ∀ a, (a, a) ∈ E)
    (hsymm : ∀ a b, (a, b) ∈ E → (b, a) ∈ E) {P : Set X}
    (hP : ∀ a b, (a, b) ∈ E → a ∈ P → b ∈ P) : IsClopen P := by
  have hopen : ∀ Q : Set X, (∀ a b, (a, b) ∈ E → a ∈ Q → b ∈ Q) → IsOpen Q := fun Q hQ =>
    isOpen_iff_mem_nhds.2 fun a ha =>
      Filter.mem_of_superset ((hE a).mem_nhds (show a ∈ {b | (a, b) ∈ E} from hrefl a))
        fun b hb => hQ a b hb ha
  exact ⟨isOpen_compl_iff.1 (hopen Pᶜ fun a b hab ha hb => ha (hP b a (hsymm a b hab) hb)),
    hopen P hP⟩

section Reach

variable {T : X → X} {E : Set (X × X)} {x : X}

/-- The points reached from `x` by a chain of positive length whose steps are `E`-close. -/
def chainReach (T : X → X) (E : Set (X × X)) (x : X) : Set X :=
  {y | Relation.TransGen (ChainStep T E) x y}

theorem mem_chainReach {y : X} :
    y ∈ chainReach T E x ↔ Relation.TransGen (ChainStep T E) x y := Iff.rfl

/-- The reached set is a union of atoms. -/
theorem mem_chainReach_of_rel (htrans : ∀ a b c, (a, b) ∈ E → (b, c) ∈ E → (a, c) ∈ E)
    {a b : X} (ha : a ∈ chainReach T E x) (hab : (a, b) ∈ E) : b ∈ chainReach T E x := by
  obtain ⟨c, hxc, hca⟩ := Relation.TransGen.tail'_iff.1 (mem_chainReach.1 ha)
  exact mem_chainReach.2 (Relation.TransGen.tail' hxc (htrans (T c) a b hca hab))

/-- The reached set `P` satisfies `T(P) ⊆ P`. -/
theorem image_chainReach_subset (hrefl : ∀ a, (a, a) ∈ E) :
    T '' chainReach T E x ⊆ chainReach T E x := by
  rintro _ ⟨y, hy, rfl⟩
  exact mem_chainReach.2 ((mem_chainReach.1 hy).tail (hrefl (T y)))

theorem apply_mem_chainReach (hrefl : ∀ a, (a, a) ∈ E) : T x ∈ chainReach T E x :=
  mem_chainReach.2 (Relation.TransGen.single (hrefl (T x)))

/-- If `E ⊆ V` and there is no `V`-chain from `x` to `x`, then `x` is not reached. -/
theorem notMem_chainReach_self {V : Set (X × X)} (hEV : E ⊆ V)
    (hx : ¬ Relation.TransGen (ChainStep T V) x x) : x ∉ chainReach T E x := fun h =>
  hx (Relation.TransGen.mono (ChainStep.mono hEV) x x (mem_chainReach.1 h))

end Reach

section Partition

variable [UniformSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]

/-- A finite clopen partition finer than an entourage: every entourage `V` of a compact Hausdorff
totally disconnected space contains an equivalence relation `E` whose classes are open. -/
theorem exists_clopenPartition_subset {V : Set (X × X)} (hV : V ∈ 𝓤 X) :
    ∃ E ⊆ V, (∀ a, IsOpen {b | (a, b) ∈ E}) ∧ (∀ a, (a, a) ∈ E) ∧
      (∀ a b, (a, b) ∈ E → (b, a) ∈ E) ∧ ∀ a b c, (a, b) ∈ E → (b, c) ∈ E → (a, c) ∈ E := by
  obtain ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV
  have hnhds : ∀ z : X,
      UniformSpace.ball z (Prod.swap ⁻¹' W) ∩ UniformSpace.ball z W ∈ 𝓝 z := fun z =>
    Filter.inter_mem (UniformSpace.ball_mem_nhds z (Filter.mem_map.1 (symm_le_uniformity hW)))
      (UniformSpace.ball_mem_nhds z hW)
  choose C hC hzC hCW using fun z =>
    (isTopologicalBasis_isClopen (X := X)).mem_nhds_iff.1 (hnhds z)
  have hC' : ∀ z, IsClopen (C z) := hC
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover C fun z _ =>
    (hC' z).isOpen.mem_nhds (hzC z)
  refine ⟨{p | ∀ i ∈ t, (p.1 ∈ C i ↔ p.2 ∈ C i)}, ?_, fun a => ?_, fun _ _ _ => Iff.rfl,
    fun _ _ h i hi => (h i hi).symm, fun _ _ _ h₁ h₂ i hi => (h₁ i hi).trans (h₂ i hi)⟩
  · rintro ⟨a, b⟩ hab
    obtain ⟨i, hi, hai⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ a))
    have h₁ : (a, i) ∈ W := (hCW i hai).1
    have h₂ : (i, b) ∈ W := (hCW i ((hab i hi).1 hai)).2
    exact hWV (SetRel.prodMk_mem_comp h₁ h₂)
  · suffices h : IsOpen (⋂ i ∈ t, {b | a ∈ C i ↔ b ∈ C i}) by
      convert h using 1
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine isOpen_biInter_finset fun i _ => ?_
    by_cases ha : a ∈ C i
    · convert (hC' i).isOpen using 1
      ext b
      simp [ha]
    · convert (hC' i).compl.isOpen using 1
      ext b
      simp [ha]

/-- **Atom-graph step.** If `x` is not chain recurrent, then `Tx ∈ P \ T(P)` for a clopen `P`
with `T(P) ⊆ P`. -/
theorem exists_isClopen_apply_mem_diff (T : X ≃ₜ X) {x : X} (hx : x ∉ chainRecurrentSet T) :
    ∃ P : Set X, IsClopen P ∧ T '' P ⊆ P ∧ T x ∈ P \ T '' P := by
  obtain ⟨V, hV, hxV⟩ : ∃ V ∈ 𝓤 X, ¬ Relation.TransGen (ChainStep T V) x x := by
    by_contra h
    exact hx fun V hV => Classical.byContradiction fun hn => h ⟨V, hV, hn⟩
  obtain ⟨E, hEV, hEo, hrefl, hsymm, htrans⟩ := exists_clopenPartition_subset hV
  refine ⟨chainReach T E x, isClopen_of_saturated hEo hrefl hsymm
    fun _ _ hab ha => mem_chainReach_of_rel htrans ha hab, image_chainReach_subset hrefl,
    apply_mem_chainReach hrefl, ?_⟩
  rintro ⟨y, hy, hyx⟩
  obtain rfl := T.injective hyx
  exact notMem_chainReach_self hEV hxV hy

/-- Printed (lem:chain-core-models): "The complement $X\setminus Y$ is covered by translates of
sets $P\setminus T(P)$, where $P$ is clopen and $T(P)\subseteq P$."  The translate is
`T⁻¹(P \ T(P))`. -/
theorem compl_chainRecurrentSet_subset (T : X ≃ₜ X) :
    (chainRecurrentSet T)ᶜ ⊆ ⋃ P ∈ {P : Set X | IsClopen P ∧ T '' P ⊆ P},
      ⋃ n : ℤ, ⇑(T.toEquiv ^ n) '' (P \ T '' P) := by
  intro x hx
  obtain ⟨P, hPc, hPT, hxP⟩ := exists_isClopen_apply_mem_diff T hx
  refine Set.mem_iUnion₂.2 ⟨P, ⟨hPc, hPT⟩, Set.mem_iUnion.2 ⟨-1, T x, hxP, ?_⟩⟩
  rw [zpow_neg_one]
  exact T.toEquiv.symm_apply_apply x

end Partition

/-- **lem:chain-core-models**, second and third sentences: "The complement $X\setminus Y$ is
covered by translates of sets $P\setminus T(P)$, where $P$ is clopen and $T(P)\subseteq P$.  Each
of these sets is wandering: its distinct integer translates are pairwise disjoint."

`Y = CR(T)` is `chainRecurrentSet T` for the uniformity of `X`.  On a compact space the compatible
uniformity is unique, so this is the printed metric notion (`isChainRecurrent_iff_metric`,
`chainRecurrentSet_eq_of_compact`).  Of the printed hypotheses on `X` (nonempty compact metrizable
zero-dimensional), only compact, Hausdorff and totally disconnected are used. -/
def PrintedChainCoreCovering : Prop :=
  ∀ (X : Type) [UniformSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (T : X ≃ₜ X),
    (chainRecurrentSet T)ᶜ ⊆ (⋃ P ∈ {P : Set X | IsClopen P ∧ T '' P ⊆ P},
        ⋃ n : ℤ, ⇑(T.toEquiv ^ n) '' (P \ T '' P)) ∧
      ∀ P : Set X, IsClopen P → T '' P ⊆ P → IsWandering T.toEquiv (P \ T '' P)

theorem printedChainCoreCovering : PrintedChainCoreCovering := by
  intro _ _ _ _ _ T
  exact ⟨compl_chainRecurrentSet_subset T, fun _ _ hP => isWandering_diff_image hP⟩

end GroupApproximation.Dynamics

#audit_axioms GroupApproximation.Dynamics.isClopen_of_saturated
#audit_axioms GroupApproximation.Dynamics.mem_chainReach_of_rel
#audit_axioms GroupApproximation.Dynamics.image_chainReach_subset
#audit_axioms GroupApproximation.Dynamics.apply_mem_chainReach
#audit_axioms GroupApproximation.Dynamics.notMem_chainReach_self
#audit_axioms GroupApproximation.Dynamics.exists_clopenPartition_subset
#audit_axioms GroupApproximation.Dynamics.exists_isClopen_apply_mem_diff
#audit_axioms GroupApproximation.Dynamics.compl_chainRecurrentSet_subset
#audit_closed_axioms GroupApproximation.Dynamics.printedChainCoreCovering
