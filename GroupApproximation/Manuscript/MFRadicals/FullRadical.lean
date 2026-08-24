import GroupApproximation.Leavitt.HilbertHotelCoverBlock

/-!
# Theorem A: a finitely presented MF black hole

There is a nontrivial finitely presented property-`(T)` group `H` with
`Res_MF(H) = H`: every homomorphism from `H` into the unitary group of a matrix
corona is trivial, for every dimension sequence, hence every homomorphism from
`H` to any MF group is trivial.

The explicit *model* is the Hilbert-hotel group `EL₁₆(L_{F₂}(1,2))`; the
finitely presented *cover* is obtained from it by the two-block construction.
The distinction matters and is kept: the model is an explicit finitely
generated group, and the cover is proved finitely presented from chosen cover
data, so the honest headline is "there exists a finitely presented Kazhdan
group with full MF radical", not "here is an explicit finite presentation".
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRadicals

/-- **Theorem A.**  A nontrivial finitely presented Kazhdan group equal to its
own MF radical. -/
theorem manuscriptTheoremA :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧ Countable G ∧ Nontrivial G ∧
        HasKazhdanPropertyT.{0, 0} G ∧
        (∀ x : G, CoronaMFInvisible x) ∧ ¬ IsOperatorMF G :=
  HilbertHotel.CoverBlock.exists_finitelyPresented_kazhdan_full_mf_radical

end MFRadicals
end Manuscript
end GroupApproximation
