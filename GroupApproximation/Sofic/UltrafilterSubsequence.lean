import GroupApproximation.Sofic.UltrafilterLimit

/-!
# KT.01 and KT.02: opening the printed proof by contradiction

The printed proof of `thm:kazhdan-transport` begins:

> suppose the conclusion fails: fix `γ₀`, `δ > 0` and an infinite `I ⊆ ℕ` with
> the commutator `≥ δ` on `I`.  Fix a free ultrafilter `ω` on `ℕ` with
> `I ∈ ω`.

The development proves the transport theorem directly rather than by
contradiction, so neither step has a counterpart there.  They are not
decoration: the whole ultraproduct route exists because a *single* generator
and a *single* threshold survive on an infinite set, and that is what makes an
ultrafilter available at all.

## Where the finiteness of the generating set is used

Failure of "for every `ε` the defect is eventually below `ε` **at every
generator**" gives, at one `ε`, infinitely many stages at which *some*
generator exceeds it -- but a priori a different generator each time.  Fixing
`γ₀` is a pigeonhole over the finite generating set, and it is the only place
finiteness of `S` enters.  Property (T) supplies that finiteness
(`exists_symmetric_generating_pair`), so nothing is assumed here that the
printed hypothesis does not already give.

The second step is then `exists_freeUltrafilter_mem`: an infinite set belongs
to some ultrafilter refining the cofinite filter.
-/

namespace GroupApproximation
namespace UltrafilterSubsequence

open Filter Topology
open UltrafilterLimit

/-- **KT.01, the extraction.**  If the defect is not eventually uniformly
small over a finite index set, then one index carries a fixed positive defect
on an infinite set of stages.

`f n γ` is the defect at stage `n` and index `γ`; the manuscript's instance is
the commutator norm at a generator. -/
theorem exists_index_infinite_defect {ι : Type*} (S : Finset ι) (f : ℕ → ι → ℝ)
    (h : ¬ ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ γ ∈ S, f n γ ≤ ε) :
    ∃ γ₀ ∈ S, ∃ δ : ℝ, 0 < δ ∧ {n : ℕ | δ ≤ f n γ₀}.Infinite := by
  obtain ⟨ε, hε, hbad⟩ : ∃ ε : ℝ, 0 < ε ∧
      ¬ ∀ᶠ n in atTop, ∀ γ ∈ S, f n γ ≤ ε := by
    by_contra hcon
    refine h fun ε hε ↦ ?_
    by_contra hb
    exact hcon ⟨ε, hε, hb⟩
  -- the stages at which some index exceeds `ε` are infinite
  have hTinf : {n : ℕ | ¬ ∀ γ ∈ S, f n γ ≤ ε}.Infinite := by
    rw [← Nat.frequently_atTop_iff_infinite]
    rwa [Filter.not_eventually] at hbad
  -- and they are covered by finitely many index-indexed sets
  have hsub : {n : ℕ | ¬ ∀ γ ∈ S, f n γ ≤ ε}
      ⊆ ⋃ γ ∈ S, {n : ℕ | ε ≤ f n γ} := by
    intro n hn
    by_contra hc
    exact hn fun γ hγ ↦ by
      by_contra hle
      exact hc (Set.mem_iUnion₂.2 ⟨γ, hγ, le_of_lt (not_le.mp hle)⟩)
  by_contra hcon
  refine hTinf (Set.Finite.subset (Set.Finite.biUnion S.finite_toSet ?_) hsub)
  intro γ hγ
  by_contra hnf
  exact hcon ⟨γ, hγ, ε, hε, hnf⟩

/-- **KT.01 and KT.02 together, as printed.**  Failure of the uniform bound
produces a single index, a single positive threshold, and a free ultrafilter
along which the defect stays above that threshold.

This is the exact opening of the printed proof, and the object it hands to the
ultraproduct construction. -/
theorem exists_freeUltrafilter_defect {ι : Type*} (S : Finset ι) (f : ℕ → ι → ℝ)
    (h : ¬ ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ γ ∈ S, f n γ ≤ ε) :
    ∃ γ₀ ∈ S, ∃ δ : ℝ, 0 < δ ∧ ∃ ω : Ultrafilter ℕ,
      (ω : Filter ℕ) ≤ cofinite ∧ ∀ᶠ n in (ω : Filter ℕ), δ ≤ f n γ₀ := by
  obtain ⟨γ₀, hγ₀, δ, hδ, hinf⟩ := exists_index_infinite_defect S f h
  obtain ⟨ω, hmem, hle⟩ := exists_freeUltrafilter_mem hinf
  exact ⟨γ₀, hγ₀, δ, hδ, ω, hle, hmem⟩

end UltrafilterSubsequence
end GroupApproximation
