import GroupApproximation.Dynamics.SubshiftWordGraph
import GroupApproximation.Meta.AxiomGuard

/-!
# Retained subshifts

sec:chain-core, proof of lem:chain-core-models.  "Retain only the cyclic edges at level `r`, and let
`Z_r` be the subshift read from bi-infinite paths in this graph."  A bi-infinite path of retained
edges is read as a configuration all of whose words of length `r + 1` are cyclic edges of the
level-`r` word graph of `X`.

"`Z_{r+1} ⊆ Z_r`, since a higher-level cycle projects to a closed walk at a lower level": the
projection `u ↦ Fin.init u` from words of length `r + 1` to words of length `r` maps edges of the
level-`(r + 1)` graph to edges of the level-`r` graph.

## Main results
* `retainedSubshift X r`: the set `Z_r`.
* `isClosed_retainedSubshift`, `mapsTo_shift_retainedSubshift`: `Z_r` is a subshift.
* `wordEdge_init`, `reflTransGen_init`: projection of edges and walks to the lower level.
* `retainedSubshift_succ_subset`: `Z_{r+1} ⊆ Z_r`.
-/

namespace GroupApproximation.ChainCore

open Set SymbolicDynamics.FullShift GroupApproximation.WordGraph

variable {A : Type*}

/-- sec:chain-core: the retained subshift `Z_r`, read from bi-infinite paths of cyclic edges of the
level-`r` word graph of `X`. -/
def retainedSubshift (X : Set (ℤ → A)) (r : ℕ) : Set (ℤ → A) :=
  {x | ∀ i : ℤ, IsCyclicEdge X r (word x i (r + 1))}

theorem retainedSubshift_eq_iInter (X : Set (ℤ → A)) (r : ℕ) :
    retainedSubshift X r =
      ⋂ i : ℤ, (fun x : ℤ → A => word x i (r + 1)) ⁻¹' {w | IsCyclicEdge X r w} :=
  by ext x; simp only [retainedSubshift, mem_iInter, mem_preimage, mem_setOf_eq]

theorem isClosed_retainedSubshift [TopologicalSpace A] [DiscreteTopology A] (X : Set (ℤ → A))
    (r : ℕ) : IsClosed (retainedSubshift X r) := by
  rw [retainedSubshift_eq_iInter]
  exact isClosed_iInter fun _ =>
    (isClosed_discrete _).preimage (continuous_pi fun _ => continuous_apply _)

theorem mapsTo_shift_retainedSubshift (X : Set (ℤ → A)) (r : ℕ) (n : ℤ) :
    MapsTo (shift n) (retainedSubshift X r) (retainedSubshift X r) := by
  intro x hx
  simp only [retainedSubshift, mem_setOf_eq] at hx ⊢
  intro i
  rw [word_shift]
  exact hx (n + i)

/-- The projection `u ↦ Fin.init u` maps edges of the level-`(r + 1)` word graph to edges of the
level-`r` word graph. -/
theorem wordEdge_init {X : Set (ℤ → A)} {r : ℕ} {u v : Fin (r + 1) → A}
    (h : wordEdge X (r + 1) u v) : wordEdge X r (Fin.init u) (Fin.init v) := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  exact ⟨Fin.init w, init_mem_language hw, rfl, Fin.tail_init_eq_init_tail w⟩

/-- A walk of the level-`(r + 1)` word graph projects to a walk of the level-`r` word graph. -/
theorem reflTransGen_init {X : Set (ℤ → A)} {r : ℕ} {u v : Fin (r + 1) → A}
    (h : Relation.ReflTransGen (wordEdge X (r + 1)) u v) :
    Relation.ReflTransGen (wordEdge X r) (Fin.init u) (Fin.init v) :=
  Relation.ReflTransGen.lift Fin.init (fun _ _ => wordEdge_init) _ _ h

/-- sec:chain-core: `Z_{r+1} ⊆ Z_r`, since a higher-level cycle projects to a closed walk at a
lower level. -/
theorem retainedSubshift_succ_subset (X : Set (ℤ → A)) (r : ℕ) :
    retainedSubshift X (r + 1) ⊆ retainedSubshift X r := by
  intro x hx
  simp only [retainedSubshift, mem_setOf_eq] at hx ⊢
  intro i
  obtain ⟨hmem, hcyc⟩ := hx i
  rw [tail_word, init_word] at hcyc
  have h := reflTransGen_init hcyc
  simp only [init_word] at h
  refine ⟨?_, ?_⟩
  · simpa only [init_word] using init_mem_language hmem
  · rwa [tail_word, init_word]

theorem retainedSubshift_antitone (X : Set (ℤ → A)) : Antitone (retainedSubshift X) :=
  antitone_nat_of_succ_le (retainedSubshift_succ_subset X)

#audit_axioms isClosed_retainedSubshift
#audit_axioms mapsTo_shift_retainedSubshift
#audit_axioms retainedSubshift_succ_subset
#audit_axioms retainedSubshift_antitone

end GroupApproximation.ChainCore
