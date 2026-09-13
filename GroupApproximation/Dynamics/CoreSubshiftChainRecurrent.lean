import GroupApproximation.Dynamics.ChainRecurrence
import GroupApproximation.Dynamics.CoreSubshift
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Order.Filter.Bases.Finite
import Mathlib.Topology.UniformSpace.DiscreteUniformity
import Mathlib.Topology.UniformSpace.Pi

/-!
# The symbolic core is the chain-recurrent set

sec:chain-core, proof of lem:chain-core-models.  "Closed approximate orbits at a prescribed window
scale give closed walks through the corresponding word.  Conversely, a cycle through a sufficiently
long word centered at `x` gives a closed approximate orbit at `x`: realize successive edges by points
of `X`, using `x` at the initial and final positions.  Overlap of the words gives the required
accuracy.  Hence `Y_0 = CR(T)`."

The alphabet carries the discrete uniformity and `X` the subtype of the product uniformity.  The
sets `windowRel X N` of pairs agreeing on `[-N, N]` form a basis of its entourages.  The map `T` on
`X` is the restriction of `shift 1`.  The chain-recurrent set is hull-euler's `chainRecurrentSet`.
On a compact space every compatible uniformity gives the same set, and for every compatible metric
its points are the printed metric chain-recurrent points.

## Main results
* `windowRel_mem_uniformity`, `exists_windowRel_subset`: the window entourages form a basis.
* `reflTransGen_word_of_transGen`: closed approximate orbits give closed walks.
* `transGen_of_reflTransGen`: walks, realized by points of `X`, give approximate orbits.
* `isChainRecurrent_iff_mem_coreSubshift`, `coreSubshift_eq_chainRecurrentSet`,
  `chainRecurrentSet_eq_preimage_coreSubshift`, `isMetricChainRecurrent_iff_mem_coreSubshift`:
  `Y_0 = CR(T)`.
-/

namespace GroupApproximation.ChainCore

open Set SymbolicDynamics.FullShift GroupApproximation.WordGraph GroupApproximation.Dynamics
open scoped Uniformity

variable {A : Type*}

/-- The pairs of points of `X` agreeing on `[-N, N]`. -/
def windowRel (X : Set (ℤ → A)) (N : ℕ) : Set (X × X) :=
  {p | ∀ i : ℤ, i.natAbs ≤ N → (p.1 : ℤ → A) i = (p.2 : ℤ → A) i}

theorem windowRel_mem_uniformity [UniformSpace A] [DiscreteUniformity A] (X : Set (ℤ → A))
    (N : ℕ) : windowRel X N ∈ 𝓤 X := by
  have h : ∀ i : ℤ, {p : X × X | (p.1 : ℤ → A) i = (p.2 : ℤ → A) i} ∈ 𝓤 X := by
    intro i
    have hi := ((Pi.uniformContinuous_proj (fun _ : ℤ => A) i).comp
      (uniformContinuous_subtype_val : UniformContinuous ((↑) : X → ℤ → A)))
      (DiscreteUniformity.relId_mem_uniformity A)
    exact Filter.mem_of_superset (Filter.mem_map.1 hi) fun _ hp => hp
  have h2 : (⋂ k : Fin (2 * N + 1), {p : X × X |
      (p.1 : ℤ → A) (((k : ℕ) : ℤ) - N) = (p.2 : ℤ → A) (((k : ℕ) : ℤ) - N)}) ∈ 𝓤 X :=
    Filter.iInter_mem.2 fun _ => h _
  refine Filter.mem_of_superset h2 fun p hp i hi => ?_
  have hk := mem_iInter.1 hp ⟨(i + N).toNat, by omega⟩
  have e : (((i + N).toNat : ℕ) : ℤ) - N = i := by omega
  simp only [mem_setOf_eq, e] at hk
  exact hk

theorem exists_windowRel_subset [UniformSpace A] [DiscreteUniformity A] {X : Set (ℤ → A)}
    {V : Set (X × X)} (hV : V ∈ 𝓤 X) : ∃ N : ℕ, windowRel X N ⊆ V := by
  rw [uniformity_subtype, Filter.mem_comap] at hV
  obtain ⟨W, hW, hWV⟩ := hV
  simp only [Pi.uniformity, DiscreteUniformity.eq_principal_setRelId, Filter.comap_principal]
    at hW
  obtain ⟨t, ht, htW⟩ := (Filter.hasBasis_iInf_principal_finite _).mem_iff.1 hW
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i ∈ t, i.natAbs ≤ N :=
    ⟨ht.toFinset.sup Int.natAbs, fun i hi => Finset.le_sup (ht.mem_toFinset.2 hi)⟩
  refine ⟨N, fun p hp => hWV ?_⟩
  show ((p.1 : ℤ → A), (p.2 : ℤ → A)) ∈ W
  apply htW
  rw [mem_iInter₂]
  intro i hi
  exact hp i (hN i hi)

/-- A step of a chain accurate on `[-N, N]`: `T a` agrees with `b` on `[-N, N]`. -/
theorem chainStep_windowRel_iff {X : Set (ℤ → A)} (hX : ∀ n : ℤ, MapsTo (shift n) X X) {N : ℕ}
    {a b : X} :
    ChainStep ((hX 1).restrict (shift 1) X X) (windowRel X N) a b ↔
      ∀ i : ℤ, i.natAbs ≤ N → (a : ℤ → A) (1 + i) = (b : ℤ → A) i := by
  simp only [ChainStep, windowRel, mem_setOf_eq, MapsTo.val_restrict_apply, shift_apply]

/-- sec:chain-core: closed approximate orbits at a prescribed window scale give closed walks through
the corresponding word.  A chain from `a` to `b` accurate on `[-N, N]` gives a walk from the word of
`a` on `[i + 1, i + r]` to the word of `b` on `[i, i + r)`, whenever `[i, i + r]` lies in
`[-N, N + 1]`. -/
theorem reflTransGen_word_of_transGen {X : Set (ℤ → A)} (hX : ∀ n : ℤ, MapsTo (shift n) X X)
    {N r : ℕ} {i : ℤ} (hi : -(N : ℤ) ≤ i) (hir : i + r ≤ N + 1) {a b : X}
    (h : Relation.TransGen (ChainStep ((hX 1).restrict (shift 1) X X) (windowRel X N)) a b) :
    Relation.ReflTransGen (wordEdge X r) (word (a : ℤ → A) (i + 1) r) (word (b : ℤ → A) i r) := by
  have key : ∀ c d : X, ChainStep ((hX 1).restrict (shift 1) X X) (windowRel X N) c d →
      word (c : ℤ → A) (i + 1) r = word (d : ℤ → A) i r := by
    intro c d hcd
    rw [chainStep_windowRel_iff hX] at hcd
    funext j
    have hj := j.isLt
    simp only [word_apply]
    rw [show i + 1 + ((j : ℕ) : ℤ) = 1 + (i + (j : ℕ)) by omega]
    exact hcd _ (by omega)
  induction h with
  | single hab =>
    exact (congrArg (Relation.ReflTransGen (wordEdge X r) (word (a : ℤ → A) (i + 1) r))
      (key _ _ hab)).mp Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    have e := wordEdge_word hX b.2 i r
    rw [key b c hbc] at e
    exact ih.tail e

/-- sec:chain-core: realize successive edges by points of `X`; overlap of the words gives the
required accuracy.  A walk from the word of `T a` on `[-N, N]` to the word of `b` on `[-N, N]`
gives a chain from `a` to `b` accurate on `[-N, N]`. -/
theorem transGen_of_reflTransGen {X : Set (ℤ → A)} (hX : ∀ n : ℤ, MapsTo (shift n) X X) {N : ℕ}
    {u v : Fin (2 * N + 1) → A} (h : Relation.ReflTransGen (wordEdge X (2 * N + 1)) u v) :
    ∀ a b : X, word (a : ℤ → A) (-(N : ℤ) + 1) (2 * N + 1) = u →
      word (b : ℤ → A) (-(N : ℤ)) (2 * N + 1) = v →
      Relation.TransGen (ChainStep ((hX 1).restrict (shift 1) X X) (windowRel X N)) a b := by
  have step : ∀ c d : X, word (c : ℤ → A) (-(N : ℤ) + 1) (2 * N + 1) =
      word (d : ℤ → A) (-(N : ℤ)) (2 * N + 1) →
      ChainStep ((hX 1).restrict (shift 1) X X) (windowRel X N) c d := by
    intro c d hcd
    rw [chainStep_windowRel_iff hX]
    intro i hi
    have h' := congrFun hcd ⟨(i + N).toNat, by omega⟩
    simp only [word_apply] at h'
    rwa [show -(N : ℤ) + 1 + (((i + N).toNat : ℕ) : ℤ) = 1 + i by omega,
      show -(N : ℤ) + (((i + N).toNat : ℕ) : ℤ) = i by omega] at h'
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro a b ha hb
    exact .single (step a b (ha.trans hb.symm))
  | head huc _ ih =>
    intro a b ha hb
    obtain ⟨w, ⟨y, hy, rfl⟩, rfl, rfl⟩ := huc
    refine .head (step a ⟨shift (N : ℤ) y, hX _ hy⟩ ?_) (ih _ b ?_ hb)
    · rw [ha, init_word]
      show word y 0 (2 * N + 1) = word (shift (N : ℤ) y) (-(N : ℤ)) (2 * N + 1)
      rw [word_shift, show (N : ℤ) + -(N : ℤ) = 0 by omega]
    · show word (shift (N : ℤ) y) (-(N : ℤ) + 1) (2 * N + 1) = _
      rw [word_shift, tail_word, show (N : ℤ) + (-(N : ℤ) + 1) = 0 + 1 by omega]

/-- sec:chain-core: `Y_0 = CR(T)`, pointwise: a point of `X` is chain recurrent exactly when it
lies in the symbolic core. -/
theorem isChainRecurrent_iff_mem_coreSubshift [UniformSpace A] [DiscreteUniformity A]
    {X : Set (ℤ → A)} (hX : ∀ n : ℤ, MapsTo (shift n) X X) (x : X) :
    IsChainRecurrent ((hX 1).restrict (shift 1) X X) x ↔ (x : ℤ → A) ∈ coreSubshift X := by
  constructor
  · intro hx
    rw [mem_coreSubshift_iff]
    intro r i
    refine ⟨word_mem_language hX x.2 i (r + 1), ?_⟩
    rw [tail_word, init_word]
    exact reflTransGen_word_of_transGen hX (N := i.natAbs + r) (by omega) (by omega)
      (hx _ (windowRel_mem_uniformity X _))
  · intro hx V hV
    obtain ⟨N, hN⟩ := exists_windowRel_subset hV
    have hc := (mem_coreSubshift_iff.1 hx (2 * N + 1) (-(N : ℤ))).2
    rw [tail_word, init_word] at hc
    exact Relation.TransGen.mono (ChainStep.mono hN) _ _
      (transGen_of_reflTransGen hX hc x x rfl rfl)

/-- sec:chain-core: `CR(T)` is the set of points of `X` lying in `Y_0`. -/
theorem chainRecurrentSet_eq_preimage_coreSubshift [UniformSpace A] [DiscreteUniformity A]
    {X : Set (ℤ → A)} (hX : ∀ n : ℤ, MapsTo (shift n) X X) :
    chainRecurrentSet ((hX 1).restrict (shift 1) X X) = ((↑) : X → ℤ → A) ⁻¹' coreSubshift X :=
  Set.ext fun x => isChainRecurrent_iff_mem_coreSubshift hX x

/-- sec:chain-core: hence `Y_0 = CR(T)`. -/
theorem coreSubshift_eq_chainRecurrentSet [UniformSpace A] [DiscreteUniformity A]
    {X : Set (ℤ → A)} (hXc : IsClosed X) (hX : ∀ n : ℤ, MapsTo (shift n) X X) :
    coreSubshift X = ((↑) : X → ℤ → A) '' chainRecurrentSet ((hX 1).restrict (shift 1) X X) := by
  ext y
  constructor
  · intro hy
    exact ⟨⟨y, coreSubshift_subset hXc hX hy⟩,
      (isChainRecurrent_iff_mem_coreSubshift hX ⟨y, coreSubshift_subset hXc hX hy⟩).2 hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (isChainRecurrent_iff_mem_coreSubshift hX x).1 hx

/-- sec:chain-core: for every compatible metric on `X`, the printed chain-recurrent points are the
points of `Y_0`. -/
theorem isMetricChainRecurrent_iff_mem_coreSubshift [UniformSpace A] [DiscreteUniformity A]
    [Finite A] {X : Set (ℤ → A)} (hXc : IsClosed X) (hX : ∀ n : ℤ, MapsTo (shift n) X X)
    (d : PseudoMetricSpace X)
    (hd : d.toUniformSpace.toTopologicalSpace = instTopologicalSpaceSubtype) (x : X) :
    @IsMetricChainRecurrent X d ((hX 1).restrict (shift 1) X X) x ↔
      (x : ℤ → A) ∈ coreSubshift X := by
  haveI := isCompact_iff_compactSpace.1 hXc.isCompact
  rw [← @isChainRecurrent_iff_metric (↥X) d,
    unique_uniformity_of_compact (t := instTopologicalSpaceSubtype)
      (u' := instUniformSpaceSubtype) hd rfl]
  exact isChainRecurrent_iff_mem_coreSubshift hX x

#audit_axioms windowRel_mem_uniformity
#audit_axioms exists_windowRel_subset
#audit_axioms isChainRecurrent_iff_mem_coreSubshift
#audit_axioms chainRecurrentSet_eq_preimage_coreSubshift
#audit_axioms coreSubshift_eq_chainRecurrentSet
#audit_axioms isMetricChainRecurrent_iff_mem_coreSubshift

end GroupApproximation.ChainCore
