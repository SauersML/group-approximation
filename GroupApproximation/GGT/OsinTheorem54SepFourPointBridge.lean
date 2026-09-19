import GroupApproximation.GGT.OsinTheorem54SepLemma49
import GroupApproximation.GGT.CayleyFourPointConverse

/-!
# The §4.2 family from the hypothesis Theorem 5.4 already makes

`GGT.OsinTheorem54SepLemma49` discharges Osin's Lemmas 4.8 and 4.9 from the
four-point condition on the alphabet.  Clause (a) of `IsHyperbolicallyEmbedded`
states hyperbolicity of `Γ(G, X ⊔ ℋ)` in the Gromov-product form on the metric
space `Cayley D.alphabet`, at a real `δ`; the passage between the two is
`GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded`, landed with
`GGT/CayleyFourPointConverse.lean`.

So this module is one line of plumbing, and its point is what the line says:
after it, neither of the assembly's two geometric binders is a hypothesis of
its own.  Both follow from `D.IsHyperbolicallyEmbedded` --- which Theorem 5.4
assumes anyway --- together with a symmetric base, for every `Dc` past `4C`.

The threshold is stated `C * 4 ≤ Dc` and not as a choice of `Dc`, because the
assembly needs `C` before it can pick `Dc`: the constant comes out of the §4.2
bound, and `Dc` is chosen with it in hand.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Lemmas 4.8 and 4.9 from hyperbolic embedding.**  Clause (a) of
Definition 4.25 is the whole of what the §4.2 tower needs. -/
theorem exists_lemmaFourEight_and_lemmaFourNine_of_isHyperbolicallyEmbedded
    [Fintype Λ] (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hemb : D.IsHyperbolicallyEmbedded) :
    ∃ C : ℕ, 0 < C ∧ ∀ Dc : ℕ, C * 4 ≤ Dc →
      (∀ lam : Λ, LemmaFourEight D lam Dc) ∧
      ∀ f g h : G, (∑ lam : Λ, sepCard D lam Dc f g)
        ≤ (∑ lam : Λ, sepCard D lam Dc f h)
          + (∑ lam : Λ, sepCard D lam Dc g h) + 2 := by
  obtain ⟨δ, hδ⟩ := exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hemb
  exact exists_lemmaFourEight_and_lemmaFourNine_of_fourPointHyperbolic D hsymm hδ

end OsinComponents
end GGT
end GroupApproximation
