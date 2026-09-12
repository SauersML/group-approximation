import Mathlib.GroupTheory.PushoutI

/-!
# Symmetric amalgamated doubles

This file defines the symmetric double `G *_Γ G` and proves its elementary
structural interface.  It contains no approximation-theoretic endpoint:
only the algebraic construction established below is exported.
-/

namespace GroupApproximation

open Monoid

universe u

variable (G : Type u) [Group G] (Γ : Subgroup G)

/-! ## The symmetric double -/

/-- The two vertex groups of the symmetric amalgam. -/
abbrev DoubleFactor : Bool → Type u := fun _ ↦ G

instance doubleFactorGroup : ∀ b, Group (DoubleFactor G b) :=
  fun _ ↦ inferInstanceAs (Group G)

/-- Both edge maps are the inclusion `Γ ↪ G`. -/
def doubleMap : ∀ b, ↥Γ →* DoubleFactor G b := fun _ ↦ Γ.subtype

theorem doubleMap_injective : ∀ b, Function.Injective (doubleMap G Γ b) :=
  fun _ ↦ Γ.subtype_injective

/-- The symmetric double `G *_Γ G`. -/
abbrev SymmetricDouble : Type u := PushoutI (doubleMap G Γ)

/-- One of the two canonical vertex-group embeddings. -/
def inDouble (b : Bool) : G →* SymmetricDouble G Γ :=
  PushoutI.of (φ := doubleMap G Γ) b

theorem inDouble_injective (b : Bool) :
    Function.Injective (inDouble G Γ b) :=
  PushoutI.of_injective (doubleMap_injective G Γ) b

instance doubleFactorCountable [Countable G] :
    ∀ b, Countable (DoubleFactor G b) := fun _ ↦ inferInstanceAs (Countable G)

instance symmetricDoubleCountable [Countable G] :
    Countable (SymmetricDouble G Γ) := by
  haveI h0 : Countable (FreeMonoid (Σ b, DoubleFactor G b)) :=
    inferInstanceAs (Countable (List (Σ b, DoubleFactor G b)))
  haveI h1 : Countable (CoprodI (DoubleFactor G)) :=
    Con.mk'_surjective.countable
  haveI h2 : Countable (FreeMonoid (CoprodI (DoubleFactor G) ⊕ ↥Γ)) :=
    inferInstanceAs (Countable (List (CoprodI (DoubleFactor G) ⊕ ↥Γ)))
  haveI h3 : Countable (Coprod (CoprodI (DoubleFactor G)) ↥Γ) :=
    Con.mk'_surjective.countable
  exact Con.mk'_surjective.countable

end GroupApproximation
