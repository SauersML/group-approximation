import GroupApproximation.CharClass.LerayHirschTransport

/-!
# `LerayHirschGraded` transports along an isomorphism of total spaces

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`cc-projective`'s instances are stated about `Proj p`.  The Thom bridge presents
the hyperplane as a **subset** of `P(p⊕1)`, so an instance has to be moved along
`cc-bundle`'s homeomorphism onto that range.

Nothing new is proved here.  `cc-projective`'s `bijective_lhSum_of_iso` is the
transport already, at the cover-induction's `lhSum`; `LerayHirschBridge` transfers
between `lhSum` and `lhMap` in both directions.  This file is the composite,
stated at the published interface `LerayHirschGraded`, with the base isomorphism
taken to be the identity because the two total spaces here sit over the *same*
base.

## Main declaration

* `LH.lerayHirschGraded_of_iso` — the transport, at the published interface.
-/

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

namespace LH

variable {X P Q : TopCat.{0}}

/-- **`LerayHirschGraded` transports along an isomorphism of total spaces over one
base.**  `e` identifies the total spaces, `hπ` says it lies over the base and `hξ`
that it carries the class to the class.  Both are equations rather than
assumptions about `e`, so the statement holds of whatever supplies them. -/
theorem lerayHirschGraded_of_iso (e : Q ≅ P)
    (π : P ⟶ X) (πQ : Q ⟶ X) (hπ : e.hom ≫ π = πQ)
    (ξ : Hmod2 P 2) (ξQ : Hmod2 Q 2) (hξ : pull e.hom 2 ξ = ξQ)
    {r : ℕ} (L : LerayHirschGraded π ξ r) : LerayHirschGraded πQ ξQ r :=
  lerayHirschGraded_of_bijective πQ ξQ r fun n =>
    bijective_lhSum_of_iso πQ π (Iso.refl X) e
      (by rw [hπ, Iso.refl_hom, Category.comp_id]) ξQ ξ hξ r n
      (bijective_lhSum_of_lhMap π ξ r n (L.bij n))

/-! Printed on every build. -/

#print axioms lerayHirschGraded_of_iso

end LH

end

end GroupApproximation.CharClass
