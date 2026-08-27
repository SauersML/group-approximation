import GroupApproximation.Sofic.FiniteActionCharacter
import Mathlib.GroupTheory.Divisible
import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite images of rootable groups

A pointwise unitary-to-permutation conversion which preserves every exact
product would be a homomorphism from a unitary group to a finite symmetric
group.  The matrix-specific input is that every unitary has an `n`th root.
This file isolates the group-theoretic endpoint: a group rootable by every
positive natural number has no nontrivial finite image.
-/

namespace GroupApproximation

variable {G F : Type*} [Group G] [RootableBy G ℕ] [Group F] [Finite F]

/-- Every homomorphism from an ℕ-rootable group to a finite group is trivial.

For an element of the finite target, take a root in the source of degree
`|F|`; its image has `|F|`th power one by Lagrange's theorem. -/
theorem hom_eq_one_of_rootableBy_finite (f : G →* F) (g : G) : f g = 1 := by
  have hcard : Nat.card F ≠ 0 := Nat.card_pos.ne'
  obtain ⟨x, hx⟩ :=
    (RootableBy.surjective_pow (A := G) (α := ℕ) hcard) g
  calc
    f g = f (x ^ Nat.card F) := congrArg f hx.symm
    _ = (f x) ^ Nat.card F := map_pow f x _
    _ = 1 := pow_card_eq_one'

/-- In particular, a homomorphism from an ℕ-rootable group to a finite
symmetric group assigns every element the identity permutation. -/
theorem permHom_eq_one_of_rootableBy_finite
    {X : Type*} [Finite X] (f : G →* Equiv.Perm X) (g : G) : f g = 1 :=
  hom_eq_one_of_rootableBy_finite f g

end GroupApproximation
