import GroupApproximation.CharClass.LerayHirschMV
import GroupApproximation.CharClass.LerayHirschTransport

/-!
# Open subspaces, and an open of an open

The induction over a finite cover shrinks the ambient space at every step, so it
has to say what an open set of the base looks like inside a smaller ambient one.
This file is that bookkeeping and nothing else: the subspace cut out by an open
set, an open set viewed inside a larger open set, and the canonical isomorphism
identifying the second with the first.

The isomorphism is the identity on points; all that happens is that a nested
subtype is flattened.  Structure eta makes both round trips definitional.

## Main declarations

* `opSpace`, `opIncl`, `opRel` — the subspace, its inclusion, and the relative open.
* `relIso` — `↥(A viewed in ↥C) ≅ ↥A`, for `A ≤ C`.
* `opRel_comap` — taking the preimage commutes with viewing an open inside a larger one.
* `opRel_sup_eq_top` — two opens cover their union.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X P : TopCat.{0}}

/-! ## 1. The subspace cut out by an open set -/

/-- The subspace of `X` cut out by an open set. -/
abbrev opSpace (A : Opens X) : TopCat.{0} := TopCat.of ((A : Opens X) : Set X)

/-- The inclusion of an open subspace. -/
abbrev opIncl (A : Opens X) : opSpace A ⟶ X := sInclusion ((A : Opens X) : Set X)

/-- An open set of `X`, viewed as an open set of the subspace cut out by `C`. -/
abbrev opRel (A C : Opens X) : Opens (opSpace C) := opensComap (opIncl C) A

@[simp] theorem mem_opRel (A C : Opens X) (x : opSpace C) :
    x ∈ opRel A C ↔ (x : X) ∈ A := Iff.rfl

/-! ## 2. Flattening a nested subtype -/

/-- **An open set inside a larger open set is itself.**  The map is the identity on
points; only the nesting of subtypes changes. -/
def relIso (A C : Opens X) (h : A ≤ C) : opSpace (opRel A C) ≅ opSpace A where
  hom := TopCat.ofHom
    ⟨fun x => ⟨((x : opSpace C) : X), x.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  inv := TopCat.ofHom
    ⟨fun y => ⟨⟨(y : X), h y.2⟩, y.2⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

@[simp] theorem relIso_hom_apply (A C : Opens X) (h : A ≤ C) (x : opSpace (opRel A C)) :
    (ConcreteCategory.hom (relIso A C h).hom) x = ⟨((x : opSpace C) : X), x.2⟩ := rfl

/-- The inclusion of the relative open into the bigger subspace, followed by that
subspace's inclusion, is the inclusion of the smaller open. -/
theorem relIso_hom_comp_opIncl (A C : Opens X) (h : A ≤ C) :
    (relIso A C h).hom ≫ opIncl A = opIncl (opRel A C) ≫ opIncl C := rfl

/-! ## 3. Preimages -/

/-- **Taking the preimage commutes with viewing an open inside a larger one.** -/
theorem opRel_comap (f : P ⟶ X) (A C : Opens X) :
    opensComap (opensRestrict f C) (opRel A C) = opRel (opensComap f A) (opensComap f C) :=
  rfl

/-- The restriction of `f` over a smaller open, read through the two flattenings, is
the restriction of `f` over that open. -/
theorem relIso_square (f : P ⟶ X) (A C : Opens X) (h : A ≤ C)
    (h' : opensComap f A ≤ opensComap f C) :
    (relIso (opensComap f A) (opensComap f C) h').hom ≫ opensRestrict f A
      = opensRestrict (opensRestrict f C) (opRel A C) ≫ (relIso A C h).hom :=
  rfl

/-! ## 4. Two opens cover their union -/

theorem le_sup_left' (A B : Opens X) : A ≤ A ⊔ B := le_sup_left

theorem le_sup_right' (A B : Opens X) : B ≤ A ⊔ B := le_sup_right

/-- **Inside their union, two opens cover.** -/
theorem opRel_sup_eq_top (A B : Opens X) :
    opRel A (A ⊔ B) ⊔ opRel B (A ⊔ B) = ⊤ := by
  refine Opens.ext (Set.eq_univ_of_forall fun x => ?_)
  have hx : (x : X) ∈ A ⊔ B := x.2
  rw [Opens.coe_sup, Set.mem_union]
  exact hx

end

end LH
end CharClass
end GroupApproximation
