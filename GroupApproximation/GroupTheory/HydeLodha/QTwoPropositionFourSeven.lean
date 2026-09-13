import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationStabK
import GroupApproximation.Meta.AxiomGuard

/-!
# Hyde–Lodha, Proposition 4.7, as printed

"For `Γ` so that `Q_n ≤ Γ ≤ Γ_n` and every nonempty finite set `K ⊂ ℤ[1/η_n]`, `Γ_K = Γ_{K+ℤ}` is of
type `F_∞`."  Here `n = 2` and `ℤ[1/η_2] = ℤ[1/6]`; type `F_∞` is read as finitely presented, which is
all that the finitely presented infinite simple subgroup `J ≤ G_0` of `non_mf_groups_exist.tex`
(line 1679) consumes.

* `stabK_eq_stabK_addIntSet`: the printed identity `Γ_K = Γ_{K+ℤ}` for `Γ ≤ Γ₂`, since elements of
  `Γ₂` commute with integer translation;
* `PrintedPropositionFourSeven`, `printedPropositionFourSeven_of_upsilon`: the printed statement from
  Lemma 4.6 (`UpsilonFinitelyPresented`) through `isFinitelyPresented_stabK_of_upsilon`.
-/

namespace GroupApproximation
namespace HydeLodha

/-- `K + ℤ`, the integer translates of `K`. -/
def addIntSet (K : Set ℚ) : Set ℚ := {t | ∃ k ∈ K, ∃ j : ℤ, t = k + j}

theorem subset_addIntSet (K : Set ℚ) : K ⊆ addIntSet K := fun k hk => ⟨k, hk, 0, by simp⟩

/-- **Hyde–Lodha, Proposition 4.7, the identity `Γ_K = Γ_{K+ℤ}`**, for `Γ ≤ Γ₂`. -/
theorem stabK_eq_stabK_addIntSet {Γ : Subgroup (Equiv.Perm ℚ)} (hΓ : Γ ≤ gammaTwo) (K : Set ℚ) :
    stabK Γ K = stabK Γ (addIntSet K) := by
  ext f
  simp only [mem_stabK]
  constructor
  · rintro ⟨hf, hfK⟩
    refine ⟨hf, ?_⟩
    rintro t ⟨k, hk, j, rfl⟩
    rw [gammaTwo_add_int (hΓ hf) k j, hfK k hk]
  · rintro ⟨hf, hfK⟩
    exact ⟨hf, fun k hk => hfK k (subset_addIntSet K hk)⟩

/-- **Hyde–Lodha, Proposition 4.7**, as printed, with type `F_∞` read as finitely presented: "For `Γ`
so that `Q_n ≤ Γ ≤ Γ_n` and every nonempty finite set `K ⊂ ℤ[1/η_n]`, `Γ_K = Γ_{K+ℤ}` is of type
`F_∞`." -/
def PrintedPropositionFourSeven : Prop :=
  ∀ Γ : Subgroup (Equiv.Perm ℚ), qTwo ≤ Γ → Γ ≤ gammaTwo → ∀ K : Set ℚ, K.Finite → K.Nonempty →
    (∀ k ∈ K, Dyadic6 k) →
      stabK Γ K = stabK Γ (addIntSet K) ∧ Group.IsFinitelyPresented ↥(stabK Γ K)

/-- **Hyde–Lodha, Proposition 4.7**, from Lemma 4.6. -/
theorem printedPropositionFourSeven_of_upsilon (hU : UpsilonFinitelyPresented) :
    PrintedPropositionFourSeven := fun _ hQ hΓ K hKfin hKne hKgrid =>
  ⟨stabK_eq_stabK_addIntSet hΓ K, isFinitelyPresented_stabK_of_upsilon hU hQ hΓ hKfin hKne hKgrid⟩

#audit_axioms GroupApproximation.HydeLodha.subset_addIntSet
#audit_axioms GroupApproximation.HydeLodha.stabK_eq_stabK_addIntSet
#audit_axioms GroupApproximation.HydeLodha.printedPropositionFourSeven_of_upsilon

end HydeLodha
end GroupApproximation
