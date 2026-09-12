import GroupApproximation.GGT.OsinTheorem54SepInhabit

/-!
# The base case of Lemma 5.10's left half

`dist_le_sep` asserts `d_{Y⊔ℋ}(f,g) ≤ 2·sep(f,g) + 1`.  At `sep(f,g) = 0` it
says the two points are one letter apart, and that is exactly the definition of
`Y` read through left-invariance: a pair separated by nothing has
`f⁻¹g ∈ Y`, so `f⁻¹g` is a letter of the enlarged alphabet.

Two steps, and the first is easy to get wrong.  `sepCard` is `Set.ncard`, which
is `0` on an INFINITE set as well as on the empty one, so `sep(f,g) = 0` does
not by itself say the separating set is empty --- that needs finiteness, which
is `sepSet_finite` over `LemmaFourEight`.  Hence the `h48` binder here, in a
lemma that otherwise looks as though it should need nothing.

The inductive step is elsewhere; this is the case it bottoms out on.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A pair separated by nothing differs by an element of `Y`.**  Left
invariance of the separating set, which is `sepSet_smul`. -/
theorem mem_Y_of_sepSet_eq_empty (D : RelGenSet G Λ) (Dc : ℕ) {f g : G}
    (h : ∀ lam : Λ, sepSet D lam Dc f g = ∅) :
    ∀ lam : Λ, sepSet D lam Dc 1 (f⁻¹ * g) = ∅ := by
  intro lam
  have hs := sepSet_smul D lam Dc f⁻¹ f g
  rw [inv_mul_cancel] at hs
  rw [hs, h lam, Set.image_empty]

/-- **A vanishing count really is an empty separating set**, given finiteness.
`Set.ncard` is `0` on an infinite set too, so this step is not free. -/
theorem sepSet_eq_empty_of_sepCard_eq_zero (D : RelGenSet G Λ) (lam : Λ)
    (Dc : ℕ) (h48 : LemmaFourEight D lam Dc) {f g : G}
    (h : sepCard D lam Dc f g = 0) : sepSet D lam Dc f g = ∅ := by
  obtain ⟨w, hw⟩ := existsGeodesicWord D f g
  exact (Set.ncard_eq_zero (sepSet_finite h48 f g hw)).mp h

/-- **The base case.**  If nothing separates `f` from `g` they are at most one
letter apart in the enlarged alphabet. -/
theorem wordDist_enlargedY_le_one (D : RelGenSet G Λ) {Dc : ℕ} (hDc : 1 ≤ Dc)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {f g : G}
    (h : ∀ lam : Λ, sepSet D lam Dc f g = ∅) :
    wordDist (enlargedY D hDc hsymm).alphabet.carrier f g ≤ 1 := by
  have hmem : f⁻¹ * g ∈ (enlargedY D hDc hsymm).alphabet.carrier :=
    Set.mem_union_left _ (mem_Y_of_sepSet_eq_empty D Dc h)
  show wordNorm (enlargedY D hDc hsymm).alphabet.carrier (f⁻¹ * g) ≤ 1
  exact wordNorm_le_one_of_mem hmem

/-- **The base case, from the count.** -/
theorem wordDist_enlargedY_le_one_of_sepCard [Fintype Λ] (D : RelGenSet G Λ)
    {Dc : ℕ} (hDc : 1 ≤ Dc) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc) {f g : G}
    (h : (∑ lam : Λ, sepCard D lam Dc f g) = 0) :
    wordDist (enlargedY D hDc hsymm).alphabet.carrier f g ≤ 1 := by
  refine wordDist_enlargedY_le_one D hDc hsymm (fun lam => ?_)
  refine sepSet_eq_empty_of_sepCard_eq_zero D lam Dc (h48 lam) ?_
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Nat.zero_le (sepCard D i Dc f g))).mp h lam (Finset.mem_univ lam)

end OsinEnlargement
end GGT
end GroupApproximation
