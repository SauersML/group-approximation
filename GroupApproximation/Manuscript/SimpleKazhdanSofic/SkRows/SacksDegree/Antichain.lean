import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SacksDegree.Degree
import GroupApproximation.Manuscript.SimpleKazhdanSofic.TuringAntichain
import GroupApproximation.Meta.AxiomGuard

/-!
# The Sacks antichain in Mathlib's poset of Turing degrees

`simple_kazhdan_sofic_group.tex`, proof of `cor:wp`, tex l.719–721:

> By a construction of Sacks, the Turing degrees contain an antichain of size
> continuum~\cite[Chapter~V]{Odifreddi}, [...]

The printed claim is about the partial order of Turing degrees. The corpus proves it over oracles
(`printedTuringAntichainContinuum`, from the perfect-tree finite-extension construction of
`Computability/PerfectTreeAntichain.lean`): a continuum family `F` of sets of naturals whose
characteristic oracles are pairwise Turing incomparable. This module pushes it through
`turingDegreeOf` into Mathlib's `TuringDegree`.

## Route

* `charDegree B`: the degree of the characteristic oracle of `B`.
* Incomparability on `F` makes `charDegree` injective on `F`, so its image has cardinality
  `#F = 𝔠` (`Cardinal.mk_image_eq_of_injOn`), and distinct image points are incomparable because
  `charDegree B ≤ charDegree C` is `B ≤_T C` (`turingDegreeOf_le_iff`).
* `mk_turingDegree`: with `mk_turingDegree_le`, there are exactly continuum many degrees, so the
  antichain has the largest possible size.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SkRows
namespace SacksDegree

/-- The Turing degree of the characteristic oracle of a set of naturals. -/
noncomputable def charDegree (B : Set ℕ) : TuringDegree :=
  turingDegreeOf (charOracle B)

/-- The characteristic degrees of the corpus Sacks family are pairwise incomparable, and the family
is injective on degrees. -/
theorem charDegree_antichain_family :
    ∃ F : Set (Set ℕ), Cardinal.mk F = Cardinal.continuum ∧ Set.InjOn charDegree F ∧
      ∀ B ∈ F, ∀ C ∈ F, charDegree B ≤ charDegree C → B = C := by
  obtain ⟨F, hF, hanti⟩ := printedTuringAntichainContinuum
  have hle : ∀ B ∈ F, ∀ C ∈ F, charDegree B ≤ charDegree C → B = C :=
    fun B hB C hC h => hanti B hB C hC ((turingDegreeOf_le_iff _ _).1 h)
  refine ⟨F, hF, ?_, hle⟩
  intro B hB C hC h
  have e : charDegree B = charDegree C := h
  exact hle B hB C hC e.le

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SacksDegree.charDegree_antichain_family

/-- **Proof of `cor:wp`, tex l.719–721, first clause** ("By a construction of Sacks, the Turing
degrees contain an antichain of size continuum"), in Mathlib's partial order `TuringDegree`. -/
theorem manuscriptSentence_sacksAntichainTuringDegree :
    ∃ A : Set TuringDegree, IsAntichain (· ≤ ·) A ∧ Cardinal.mk A = Cardinal.continuum := by
  obtain ⟨F, hF, hinj, hle⟩ := charDegree_antichain_family
  refine ⟨charDegree '' F, ?_, ?_⟩
  · rintro _ ⟨B, hB, rfl⟩ _ ⟨C, hC, rfl⟩ hne hBC
    have hBC' : charDegree B ≤ charDegree C := hBC
    exact hne (by rw [hle B hB C hC hBC'])
  · rw [Cardinal.mk_image_eq_of_injOn _ _ hinj, hF]

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SacksDegree.manuscriptSentence_sacksAntichainTuringDegree

/-- There are exactly continuum many Turing degrees; so the Sacks antichain has the largest
possible cardinality. -/
theorem mk_turingDegree : Cardinal.mk TuringDegree = Cardinal.continuum := by
  refine le_antisymm mk_turingDegree_le ?_
  obtain ⟨A, -, hA⟩ := manuscriptSentence_sacksAntichainTuringDegree
  rw [← hA]
  exact Cardinal.mk_set_le A

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SacksDegree.mk_turingDegree

end SacksDegree
end SkRows
end SimpleKazhdanSofic
end GroupApproximation
