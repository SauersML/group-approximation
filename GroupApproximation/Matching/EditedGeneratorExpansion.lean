import GroupApproximation.Matching.EdgeWitnessDistance
import GroupApproximation.Matching.PartialEquivarianceBoundary
import GroupApproximation.Criterion.Criterion

/-!
# Tagged expansion after a small graph edit

The occurrence boundary of a generator graph remembers its generator tag.
Consequently it is exactly the tagged boundary used for partial
intertwiners.  If that generator graph is close to an expanding graph, the
edit-distance boundary inequality gives expansion above every scale on which
the edit error is small.
-/

namespace GroupApproximation

variable {G : Type} [Group G] {Y : FiniteModel}

/-- Generator-graph boundary occurrences and tagged action-boundary
occurrences are the same finite set, with only their subtype packaging
changed. -/
theorem card_taggedBoundary_generatorAction
    (T : Finset G) (act : G → Equiv.Perm Y) (A : Finset Y) :
    (FinitePartialBijection.taggedBoundary
      (fun t : T ↦ act t.1) A).card =
      (generatorGraph Y T act).boundaryCard A := by
  classical
  apply Finset.card_bij
    (fun p hp ↦
      (⟨(p.1, p.2), by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hfix
        rw [FinitePartialBijection.mem_taggedBoundary] at hp
        simp [hfix] at hp⟩ : (generatorGraph Y T act).edge))
  · intro p hp
    rw [FinitePartialBijection.mem_taggedBoundary] at hp
    rw [FiniteMultiGraph.boundary, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr ⟨hp.2, hp.1⟩
  · intro p _ q _ hpq
    exact congrArg Subtype.val hpq
  · intro e he
    have hcross := (Finset.mem_filter.mp he).2
    let p : T × Y := e.1
    have hp : p ∈ FinitePartialBijection.taggedBoundary
        (fun t : T ↦ act t.1) A := by
      rw [FinitePartialBijection.mem_taggedBoundary]
      rcases hcross with hcross | hcross
      · exact Or.inl hcross
      · exact Or.inr ⟨hcross.2, hcross.1⟩
    refine ⟨p, hp, ?_⟩
    apply Subtype.ext
    rfl

/-- A generator action inherits tagged expansion above scale `m` from an
expanding graph within edit distance less than `h * m / 2`.  The factor four
is the sole loss in the boundary comparison. -/
theorem hasTaggedExpansionAtScale_of_editDistance
    (T : Finset G) (act : G → Equiv.Perm Y) (X : FiniteMultiGraph)
    (e : Y ≃ X.vertex) {h : ℝ} {m : ℕ}
    (hX : X.HasCheegerLowerBound h)
    (hedit : (((generatorGraph Y T act).editDistance X e : ℕ) : ℝ) <
      h * m / 2) :
    FinitePartialBijection.HasTaggedExpansionAtScale
      (fun t : T ↦ act t.1) (h / 4) m := by
  refine ⟨div_pos hX.1 (by norm_num), fun A hm hhalf ↦ ?_⟩
  by_cases hA : A.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp [FinitePartialBijection.taggedBoundary]
  let A' : Finset X.vertex := A.map e.toEmbedding
  have hcard : A'.card = A.card := Finset.card_map _
  have hhalf' : 2 * A'.card ≤ Fintype.card X.vertex := by
    rw [hcard, Fintype.card_congr e.symm]
    exact hhalf
  have hA' : A'.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨e a, Finset.mem_map.mpr ⟨a, ha, rfl⟩⟩
  have hexpand := hX.2 A' hA' hhalf'
  have hboundary :=
    FiniteMultiGraph.boundaryCard_transport_le_two_mul_add_editDistance
      (generatorGraph Y T act) X e A
  have htransport :
      (X.transport Y e.symm).boundaryCard A = X.boundaryCard A' := by
    have hmap : A'.map e.symm.toEmbedding = A := by
      ext y
      simp [A']
    rw [← hmap, FiniteMultiGraph.transport_boundaryCard]
  rw [htransport] at hboundary
  have hmReal : (m : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hm
  have herror : (((generatorGraph Y T act).editDistance X e : ℕ) : ℝ) <
      h * A.card / 2 := by
    have := mul_le_mul_of_nonneg_left hmReal hX.1.le
    linarith
  have hboundaryReal : (X.boundaryCard A' : ℝ) ≤
      2 * ((generatorGraph Y T act).boundaryCard A : ℝ) +
        ((generatorGraph Y T act).editDistance X e : ℕ) := by
    exact_mod_cast hboundary
  have hgraph : h / 4 * (A.card : ℝ) ≤
      ((generatorGraph Y T act).boundaryCard A : ℝ) := by
    rw [hcard] at hexpand
    linarith
  rw [card_taggedBoundary_generatorAction]
  exact hgraph

end GroupApproximation
