import GroupApproximation.Sofic.OsinRelativeSmallCancellation
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Coprod.Basic

/-!
# Why the router is not a small-cancellation quotient of a free product

The obvious reading of the bespoke routing lemma is: form `E ∗ B`, impose a
metric `C'(1/6)` family of relators mixing the two factors, and read the common
quotient off the result.  **That reading is impossible**, and this module
proves it.

`OsinRelativeSmallCancellation.factorMap_injective_of_cyclicallyReduced` says
that under the Greendlinger length bound — which is exactly what a proof of the
`C'(1/6)` gate delivers — every factor of a free product stays embedded in the
quotient.  The routing interface, meanwhile, demands `defect_top`
(`N.map route = ⊤`), and a subgroup's image is inside the range, so the routing
map out of the source factor is forced to be onto.  Injective and onto is
bijective: the source factor *is* the routed quotient
(`factorMulEquiv`), and the designated normal subgroup already filled the
factor before any relator was imposed (`defect_eq_top_of_surjective`).

So a single free-product small-cancellation quotient can never be a *proper*
common quotient of its two factors: whichever factor surjects is isomorphic to
the quotient, and the other factor's surjection then makes the two factors
isomorphic.  Any construction that collapses the source has to do the
collapsing elsewhere — which is why `Sofic.BespokeRouterConstruction` works
over the free group on two generators and defines its two maps by their values
on generators, instead of inheriting them from factor inclusions.

Nothing here is conditional on the open gate in the weak direction: the
hypothesis is the length bound, so the theorem reads "if the gate is ever
proved, this route is dead", which is the useful direction.

The second section is unrelated bookkeeping that the same investigation
produced: Mathlib's finite-presentation instance for free products is stated
for the binary `Monoid.Coprod`, its module docstring lists the comparison with
the indexed `Monoid.CoprodI` as a TODO, and the repo's word combinatorics is
stated over `CoprodI`.  `coprodIBoolEquiv` supplies the comparison for a
two-element index and `isFinitelyPresented_coprodI_bool` the instance that
follows.
-/

namespace GroupApproximation
namespace FreeProductRouterObstruction

open Monoid Monoid.CoprodI OsinSmallCancellation

/-! ## 1.  The obstruction -/

section Obstruction

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)]

/-- **A factor that surjects onto the quotient is isomorphic to it.**  The
injectivity is the free-product small-cancellation embedding clause; the
surjectivity is what the routing interface demands. -/
theorem factorMap_bijective_of_surjective {R : Set (Word G)}
    (hcyc : ∀ r ∈ R, IsCyclicallyReduced r) (hG : GreendlingerLengthBound R)
    (i : ι) (hsurj : Function.Surjective (factorMap (relatorSubgroup R) i)) :
    Function.Bijective (factorMap (relatorSubgroup R) i) :=
  ⟨factorMap_injective_of_cyclicallyReduced hG hcyc i, hsurj⟩

/-- The source factor *is* the routed quotient. -/
noncomputable def factorMulEquiv {R : Set (Word G)}
    (hcyc : ∀ r ∈ R, IsCyclicallyReduced r) (hG : GreendlingerLengthBound R)
    (i : ι) (hsurj : Function.Surjective (factorMap (relatorSubgroup R) i)) :
    G i ≃* (CoprodI G ⧸ relatorSubgroup R) :=
  MulEquiv.ofBijective _ (factorMap_bijective_of_surjective hcyc hG i hsurj)

/-- **The small-cancellation stage contributes nothing to saturation.**  If a
subgroup of a factor fills the quotient, it already filled the factor: the
relator family cannot have collapsed anything on that side. -/
theorem defect_eq_top_of_surjective {R : Set (Word G)} {i : ι}
    (hcyc : ∀ r ∈ R, IsCyclicallyReduced r) (hG : GreendlingerLengthBound R)
    (hsurj : Function.Surjective (factorMap (relatorSubgroup R) i))
    {M : Subgroup (G i)} (hM : M.map (factorMap (relatorSubgroup R) i) = ⊤) :
    M = ⊤ := by
  obtain ⟨hinj, -⟩ := factorMap_bijective_of_surjective hcyc hG i hsurj
  have h2 : (⊤ : Subgroup (G i)).map (factorMap (relatorSubgroup R) i) = ⊤ :=
    Subgroup.map_top_of_surjective _ hsurj
  exact Subgroup.map_injective hinj (hM.trans h2.symm)

/-- **Two factors that both surject are isomorphic.**  A proper common quotient
of two non-isomorphic groups is never a metric small-cancellation quotient of
their free product. -/
noncomputable def factorsMulEquiv {R : Set (Word G)}
    (hcyc : ∀ r ∈ R, IsCyclicallyReduced r) (hG : GreendlingerLengthBound R)
    {i j : ι} (hi : Function.Surjective (factorMap (relatorSubgroup R) i))
    (hj : Function.Surjective (factorMap (relatorSubgroup R) j)) :
    G i ≃* G j :=
  (factorMulEquiv hcyc hG i hi).trans (factorMulEquiv hcyc hG j hj).symm

end Obstruction

/-! ## 2.  The indexed free product over a two-element index

Bookkeeping the same investigation produced, and a gap in Mathlib closed for
the repo's own use. -/

section BoolCoprod

universe u

variable (G : Bool → Type u) [∀ b, Group (G b)]

/-- The two factor inclusions into the binary coproduct. -/
def toCoprodFactor : ∀ b : Bool, G b →* Monoid.Coprod (G false) (G true)
  | false => Monoid.Coprod.inl
  | true => Monoid.Coprod.inr

/-- **The indexed free product over `Bool` is the binary coproduct.**
`Mathlib.GroupTheory.Coprod.Basic` lists this comparison in its own TODO list;
it is two applications of the two universal properties. -/
def coprodIBoolEquiv : CoprodI G ≃* Monoid.Coprod (G false) (G true) :=
  MonoidHom.toMulEquiv (CoprodI.lift (toCoprodFactor G))
    (Monoid.Coprod.lift (CoprodI.of (M := G) (i := false))
      (CoprodI.of (M := G) (i := true)))
    (CoprodI.ext_hom _ _ (by
      intro b
      rw [MonoidHom.comp_assoc, CoprodI.lift_comp_of, MonoidHom.id_comp]
      cases b <;> rfl))
    (Monoid.Coprod.hom_ext
      (by
        rw [MonoidHom.comp_assoc, Monoid.Coprod.lift_comp_inl,
          MonoidHom.id_comp]
        exact CoprodI.lift_comp_of (toCoprodFactor G) false)
      (by
        rw [MonoidHom.comp_assoc, Monoid.Coprod.lift_comp_inr,
          MonoidHom.id_comp]
        exact CoprodI.lift_comp_of (toCoprodFactor G) true))

/-- **A free product of two finitely presented groups is finitely presented**,
in the indexed form the repo's word combinatorics uses. -/
theorem isFinitelyPresented_coprodI_bool
    [Group.IsFinitelyPresented (G false)] [Group.IsFinitelyPresented (G true)] :
    Group.IsFinitelyPresented (CoprodI G) :=
  Group.IsFinitelyPresented.equiv (coprodIBoolEquiv G).symm

end BoolCoprod

end FreeProductRouterObstruction
end GroupApproximation
