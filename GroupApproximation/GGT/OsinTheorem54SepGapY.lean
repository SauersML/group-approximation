import GroupApproximation.GGT.OsinTheorem54SepLemma59
import GroupApproximation.GGT.OsinTheorem54SepSmul

/-!
# The gap element lies in Osin's `Y`

Lemma 5.9 says the segment between two consecutive separating cosets separates
nothing.  What Lemma 5.10 consumes is one step further on: the ELEMENT that
segment spells lies in

  `Y = {y | S(1,y;D) = ∅}`,

so it is a letter of the enlarged alphabet.  The step between the two is
left-invariance of the separating set, which is `sepSet_smul`: translating both
endpoints by `(vertex f w k)⁻¹` carries `S(vertex f w k, vertex f w j)` onto
`S(1, gap)` and the empty set to the empty set.

That is the whole bridge from 5.9 to the enlarged base, and with it the
`2n + 1` count has all its letters: the gaps are `Y`-letters by this, and the
crossings are `ℋ`-letters because a component's span lies in `H_lam`.

Conditional on `LemmaFourEight`, inherited from Lemma 5.9 and from nowhere else.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The gap between consecutive separating cosets is a letter of `Y`.** -/
theorem sepSet_gap_one_eq_empty (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ)
    {f g : G} {w : List (RelLetter G Λ)}
    (hw : IsGeodesicWord D f g w) {i k j l : ℕ}
    (hc : IsComp lam w i k) (hc' : IsComp lam w j l) (hkj : k ≤ j)
    (hsucc : SepSucc D lam Dc f g (QuotientGroup.mk (vertex f w i))
      (QuotientGroup.mk (vertex f w j))) :
    sepSet D lam Dc 1 ((vertex f w k)⁻¹ * vertex f w j) = ∅ := by
  have h := sepSet_smul D lam Dc (vertex f w k)⁻¹ (vertex f w k) (vertex f w j)
  rw [inv_mul_cancel] at h
  rw [h, sepSet_gap_eq_empty D lam Dc hw hc hc' hkj hsucc, Set.image_empty]

end OsinComponents
end GGT
end GroupApproximation
