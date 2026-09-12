import GroupApproximation.Matching.EditedGeneratorExpansion

/-!
# Pruning a label action that is close to an expander

Kun's decomposition makes the edited graph on a component an expander, while
the completed generator labels on that component differ from it by a small
edit budget.  A set smaller than the budget can carry no label boundary at all,
so the labels themselves satisfy no Cheeger bound.

`exists_prune` removes one maximal sparse cut `U`.  Suppose every nonempty set
`A` of at most half the points satisfies `h |A| ≤ 2 |∂A| + B`, where `∂A` is the
tagged label boundary, and `10 B ≤ h |Y|`.  Then `h |U| ≤ 2 B`, and every
nonempty set `W` disjoint from `U`, of at most half the remaining points, has
`h |W|` at most eight times the number of label arcs that cross `W` with both
endpoints outside `U`.

`cheeger_le_two_mul_taggedBoundary_add_editDistance` gives the additive bound
from an expanding graph at edit distance `B` from the generator graph.
-/

namespace GroupApproximation
namespace SequentialComponentFamily

open FinitePartialBijection

variable {L : Type*} [Fintype L] {Y : FiniteModel}

/-- Label arcs crossing `W` whose two endpoints both lie outside `U`. -/
noncomputable def innerBoundary (act : L → Equiv.Perm Y) (U W : Finset Y) :
    Finset (L × Y) :=
  (taggedBoundary act W).filter fun p ↦ p.2 ∉ U ∧ act p.1 p.2 ∉ U

theorem mem_innerBoundary (act : L → Equiv.Perm Y) (U W : Finset Y) (p : L × Y) :
    p ∈ innerBoundary act U W ↔
      ((p.2 ∈ W ∧ act p.1 p.2 ∉ W) ∨ (p.2 ∉ W ∧ act p.1 p.2 ∈ W)) ∧
        p.2 ∉ U ∧ act p.1 p.2 ∉ U := by
  rw [innerBoundary, Finset.mem_filter, mem_taggedBoundary]

/-- A label arc crossing `U ∪ W` crosses `U`, or crosses `W` with both
endpoints outside `U`. -/
theorem card_taggedBoundary_union_le (act : L → Equiv.Perm Y) (U W : Finset Y) :
    (taggedBoundary act (U ∪ W)).card ≤
      (taggedBoundary act U).card + (innerBoundary act U W).card := by
  classical
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro p hp
  rw [mem_taggedBoundary] at hp
  rw [Finset.mem_union, mem_taggedBoundary, mem_innerBoundary]
  by_cases hxU : p.2 ∈ U
  · refine Or.inl (Or.inl ⟨hxU, fun hyU ↦ ?_⟩)
    rcases hp with ⟨_, hout⟩ | ⟨hin, _⟩
    · exact hout (Finset.mem_union_left W hyU)
    · exact hin (Finset.mem_union_left W hxU)
  by_cases hyU : act p.1 p.2 ∈ U
  · exact Or.inl (Or.inr ⟨hxU, hyU⟩)
  refine Or.inr ⟨?_, hxU, hyU⟩
  rcases hp with ⟨hin, hout⟩ | ⟨hin, hout⟩
  · refine Or.inl ⟨?_, fun hyW ↦ hout (Finset.mem_union_right U hyW)⟩
    rcases Finset.mem_union.mp hin with hmem | hmem
    · exact absurd hmem hxU
    · exact hmem
  · refine Or.inr ⟨fun hxW ↦ hin (Finset.mem_union_right U hxW), ?_⟩
    rcases Finset.mem_union.mp hout with hmem | hmem
    · exact absurd hmem hyU
    · exact hmem

/-- **Pruning.**  If the Cheeger bound `h` holds for the tagged label boundary
up to the additive error `B`, and `10 B ≤ h |Y|`, then one set `U` with
`h |U| ≤ 2 B` can be removed so that every nonempty set of at most half the
remaining points has inner label boundary at least `h / 8` times its size. -/
theorem exists_prune (act : L → Equiv.Perm Y) {h B : ℝ} (hh : 0 < h) (hB : 0 ≤ B)
    (hexp : ∀ A : Finset Y, A.Nonempty → 2 * A.card ≤ Fintype.card Y →
      h * A.card ≤ 2 * ((taggedBoundary act A).card : ℝ) + B)
    (hsmall : 10 * B ≤ h * Fintype.card Y) :
    ∃ U : Finset Y, h * U.card ≤ 2 * B ∧
      ∀ W : Finset Y, W.Nonempty → Disjoint U W →
        2 * W.card ≤ Fintype.card Y - U.card →
          h * W.card ≤ 8 * ((innerBoundary act U W).card : ℝ) := by
  classical
  have htbEmpty : taggedBoundary act (∅ : Finset Y) = ∅ := by
    ext p
    simp
  have hempty : (∅ : Finset Y) ∈ Finset.univ.filter (fun U : Finset Y ↦
      2 * U.card ≤ Fintype.card Y ∧
        4 * ((taggedBoundary act U).card : ℝ) ≤ h * U.card) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp, by rw [htbEmpty]; simp⟩
  obtain ⟨U, hUmem, hUmax⟩ := Finset.exists_max_image _ Finset.card ⟨∅, hempty⟩
  obtain ⟨hUhalf, hUsparse⟩ := (Finset.mem_filter.mp hUmem).2
  have hUcard : h * U.card ≤ 2 * B := by
    by_cases hUne : U.Nonempty
    · have hU := hexp U hUne hUhalf
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hUne, Finset.card_empty, Nat.cast_zero,
        mul_zero]
      linarith
  refine ⟨U, hUcard, fun W hWne hUW hWhalf ↦ ?_⟩
  by_contra hcon
  have hlt : 8 * ((innerBoundary act U W).card : ℝ) < h * W.card := not_le.mp hcon
  have hWpos : 0 < W.card := Finset.card_pos.mpr hWne
  have hUWcard : (U ∪ W).card = U.card + W.card := Finset.card_union_of_disjoint hUW
  have hunionReal : ((taggedBoundary act (U ∪ W)).card : ℝ) ≤
      (taggedBoundary act U).card + (innerBoundary act U W).card := by
    exact_mod_cast card_taggedBoundary_union_le act U W
  by_cases hbig : 2 * (U ∪ W).card ≤ Fintype.card Y
  · have hUWReal : ((U ∪ W).card : ℝ) = U.card + W.card := by
      exact_mod_cast hUWcard
    have hmem : U ∪ W ∈ Finset.univ.filter (fun U : Finset Y ↦
        2 * U.card ≤ Fintype.card Y ∧
          4 * ((taggedBoundary act U).card : ℝ) ≤ h * U.card) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbig, ?_⟩
      rw [hUWReal]
      have hWnonneg : (0 : ℝ) ≤ h * W.card := mul_nonneg hh.le (Nat.cast_nonneg _)
      linarith
    have hle := hUmax (U ∪ W) hmem
    omega
  · have hVcard : (Finset.univ \ (U ∪ W)).card = Fintype.card Y - (U ∪ W).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have hVne : (Finset.univ \ (U ∪ W)).Nonempty := by
      rw [← Finset.card_pos, hVcard]
      omega
    have hVhalf : 2 * (Finset.univ \ (U ∪ W)).card ≤ Fintype.card Y := by
      rw [hVcard]
      omega
    have hV := hexp _ hVne hVhalf
    rw [taggedBoundary_compl] at hV
    have hWV : W.card ≤ (Finset.univ \ (U ∪ W)).card := by
      rw [hVcard]
      omega
    have hYV : Fintype.card Y ≤ U.card + 2 * (Finset.univ \ (U ∪ W)).card := by
      rw [hVcard]
      omega
    have hWVReal : (W.card : ℝ) ≤ (Finset.univ \ (U ∪ W)).card := by
      exact_mod_cast hWV
    have hYVReal : (Fintype.card Y : ℝ) ≤ U.card + 2 * (Finset.univ \ (U ∪ W)).card := by
      exact_mod_cast hYV
    have e1 := mul_le_mul_of_nonneg_left hWVReal hh.le
    have e2 := mul_le_mul_of_nonneg_left hYVReal hh.le
    linarith

/-- The additive Cheeger bound for a generator action within edit distance of
an expanding graph. -/
theorem cheeger_le_two_mul_taggedBoundary_add_editDistance {G : Type} [Group G]
    (T : Finset G) (act : G → Equiv.Perm Y) (X : FiniteMultiGraph) (e : Y ≃ X.vertex)
    {h : ℝ} (hX : X.HasCheegerLowerBound h) (A : Finset Y) (hA : A.Nonempty)
    (hhalf : 2 * A.card ≤ Fintype.card Y) :
    h * A.card ≤ 2 * ((taggedBoundary (fun t : T ↦ act t.1) A).card : ℝ) +
      (((generatorGraph Y T act).editDistance X e : ℕ) : ℝ) := by
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
  have hboundaryReal : (X.boundaryCard A' : ℝ) ≤
      2 * ((generatorGraph Y T act).boundaryCard A : ℝ) +
        ((generatorGraph Y T act).editDistance X e : ℕ) := by
    exact_mod_cast hboundary
  rw [hcard] at hexpand
  rw [card_taggedBoundary_generatorAction]
  linarith

end SequentialComponentFamily
end GroupApproximation
