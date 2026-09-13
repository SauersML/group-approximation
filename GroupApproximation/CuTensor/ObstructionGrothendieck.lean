import GroupApproximation.CuTensor.CuZModelCompact
import GroupApproximation.CuTensor.RankTwoObstruction
import GroupApproximation.KTheory.Basic

/-!
# From an embedding in `ℕ` to an embedding of the Grothendieck group in `ℤ`

The last algebraic step of the obstruction to `Cu(A ⊗ B) ≅ Cu(𝒵)`.  If an isomorphism
`Cu(F) ≅ Cu(𝒵)` is fed the Murray--von Neumann monoid `V(F)` of a stably finite algebra `F`,
then `CuZModel.exists_injective_addMonoidHom_nat_of_orderIso` turns it into an additive injection
`V(F) → ℕ`.  This file passes from that injection to the Grothendieck group: the lift of
`V(F) → ℕ → ℤ` to `K₀(F) = Gr V(F)` is injective.  So `K₀(F)` embeds in `ℤ`, it has no torsion,
and it contains no copy of `ℤ²` (`not_injective_of_intProdInt_embedding`).

The proof is the elementary one: every element of the Grothendieck group is a difference
`of a - of b`, and the lift sends it to `φ a - φ b`, which vanishes only when `a = b`.

## Main results

* `injective_grothendieckAddGroup_lift_natCast`: an additive injection `M → ℕ` lifts to an
  additive injection `Gr M → ℤ`;
* `not_injective_intProdInt_grothendieckAddGroup`: then no additive map `ℤ × ℤ → Gr M` is
  injective;
* `not_injective_intProdInt_of_orderIso_cuZModel`: the same from an additive order isomorphism
  with the model of `Cu(𝒵)` and an additive injection `M → Cu` with compact image;
* `not_injective_intProdInt_kZero_of_orderIso_cuZModel`: the same for `K₀` in the projection
  picture, with `M = V(F)`.
-/

namespace GroupApproximation
namespace CuTensor

open Algebra

variable {M : Type*} [AddCommMonoid M]

/-- The lift to the Grothendieck group extends the monoid homomorphism. -/
theorem grothendieckAddGroup_lift_of {G : Type*} [AddCommGroup G] (f : M →+ G) (a : M) :
    GrothendieckAddGroup.lift f (GrothendieckAddGroup.of a) = f a :=
  DFunLike.congr_fun (GrothendieckAddGroup.lift.symm_apply_apply f) a

/-- **Every element of the Grothendieck group is a difference of classes.** -/
theorem grothendieckAddGroup_exists_eq_of_sub_of (x : GrothendieckAddGroup M) :
    ∃ a b : M, x = GrothendieckAddGroup.of a - GrothendieckAddGroup.of b :=
  ⟨((AddLocalization.addMonoidOf (⊤ : AddSubmonoid M)).sec x).1,
    ((AddLocalization.addMonoidOf (⊤ : AddSubmonoid M)).sec x).2,
    eq_sub_of_add_eq
      (AddSubmonoid.LocalizationMap.sec_spec (f := AddLocalization.addMonoidOf ⊤) x)⟩

/-- **An additive injection into `ℕ` lifts to an additive injection of the Grothendieck group
into `ℤ`.** -/
theorem injective_grothendieckAddGroup_lift_natCast {φ : M →+ ℕ} (hφ : Function.Injective φ) :
    Function.Injective (GrothendieckAddGroup.lift ((Nat.castAddMonoidHom ℤ).comp φ)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨a, b, rfl⟩ := grothendieckAddGroup_exists_eq_of_sub_of x
  rw [map_sub, grothendieckAddGroup_lift_of, grothendieckAddGroup_lift_of, sub_eq_zero] at hx
  have hcast : ((φ a : ℕ) : ℤ) = ((φ b : ℕ) : ℤ) := hx
  rw [hφ (Nat.cast_injective hcast), sub_self]

/-- An additive injection into `ℕ` makes the canonical map to the Grothendieck group injective. -/
theorem grothendieckAddGroup_of_injective_of_injective_nat {φ : M →+ ℕ}
    (hφ : Function.Injective φ) :
    Function.Injective (GrothendieckAddGroup.of : M →+ GrothendieckAddGroup M) := fun a b h => by
  have h' := congrArg (GrothendieckAddGroup.lift ((Nat.castAddMonoidHom ℤ).comp φ)) h
  rw [grothendieckAddGroup_lift_of, grothendieckAddGroup_lift_of] at h'
  have hcast : ((φ a : ℕ) : ℤ) = ((φ b : ℕ) : ℤ) := h'
  exact hφ (Nat.cast_injective hcast)

/-- An additive injection into `ℕ` leaves the Grothendieck group torsion-free. -/
theorem grothendieckAddGroup_eq_zero_of_nsmul_eq_zero {φ : M →+ ℕ} (hφ : Function.Injective φ)
    {x : GrothendieckAddGroup M} {n : ℕ} (hn : n ≠ 0) (hx : n • x = 0) : x = 0 := by
  refine (injective_iff_map_eq_zero _).1 (injective_grothendieckAddGroup_lift_natCast hφ) x ?_
  have h := congrArg (GrothendieckAddGroup.lift ((Nat.castAddMonoidHom ℤ).comp φ)) hx
  rw [map_nsmul, map_zero, nsmul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 hn)

/-- **An additive injection into `ℕ` leaves no room for `ℤ²` in the Grothendieck group.** -/
theorem not_injective_intProdInt_grothendieckAddGroup {φ : M →+ ℕ} (hφ : Function.Injective φ)
    (g : ℤ × ℤ →+ GrothendieckAddGroup M) : ¬ Function.Injective g := fun hg =>
  not_injective_of_intProdInt_embedding g hg _ (injective_grothendieckAddGroup_lift_natCast hφ)

/-- **The abstract obstruction.**  Let `e : α ≃o CuZModel` be an additive order isomorphism with
the model of `Cu(𝒵)`, and let `j : M → α` be an additive injection with compact image.  Then the
Grothendieck group of `M` contains no copy of `ℤ²`. -/
theorem not_injective_intProdInt_of_orderIso_cuZModel {α : Type*} [Preorder α] [AddZeroClass α]
    (e : α ≃o CuZModel) (he0 : e 0 = 0) (he : ∀ x y, e (x + y) = e x + e y) (j : M →+ α)
    (hj : Function.Injective j) (hc : ∀ m, IsCompactElem (j m))
    (g : ℤ × ℤ →+ GrothendieckAddGroup M) : ¬ Function.Injective g := by
  obtain ⟨φ, hφ⟩ := CuZModel.exists_injective_addMonoidHom_nat_of_orderIso e he0 he j hj hc
  exact not_injective_intProdInt_grothendieckAddGroup hφ g

/-- **The obstruction for `K₀`.**  If the Murray--von Neumann monoid `V(F)` maps additively and
injectively, with compact image, into an ordered monoid additively order isomorphic to the model of
`Cu(𝒵)`, then `K₀(F)` contains no copy of `ℤ²`. -/
theorem not_injective_intProdInt_kZero_of_orderIso_cuZModel {F α : Type*} [NonUnitalSemiring F]
    [StarRing F] [Preorder α] [AddZeroClass α] (e : α ≃o CuZModel) (he0 : e 0 = 0)
    (he : ∀ x y, e (x + y) = e x + e y) (j : KTheory.VMonoid F →+ α)
    (hj : Function.Injective j) (hc : ∀ m, IsCompactElem (j m))
    (g : ℤ × ℤ →+ KTheory.KZero F) : ¬ Function.Injective g :=
  not_injective_intProdInt_of_orderIso_cuZModel e he0 he j hj hc g

end CuTensor
end GroupApproximation
