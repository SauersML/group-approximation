import GroupApproximation.Pestov91.SubshiftAlgebra
import GroupApproximation.Pestov91.CrossedProductFG
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# The witness ring `R = LC(X, 𝔽₂) ⋊ ℤ` for Pestov 9.1

`X` is the Toeplitz subshift of `GroupApproximation.Pestov91.Subshift`.  The generator of `ℤ`
acts on locally constant functions by translation, `(ofAdd j • f) x = f (shiftBy (-j) x)`, and
the witness ring is the crossed product of `GroupApproximation.Pestov91.CrossedProduct`:

  `WitnessRing = SkewMonoidAlgebra (LocallyConstant X (ZMod 2)) (Multiplicative ℤ)`.

* `witnessAction`: the action of `ℤ` on `LocallyConstant X K`, for every semiring `K`;
* `witnessAction_apply`: `(ofAdd j • f) x = f (shiftBy (-j) x)`, so the shift of the dynamics
  is `τ j = shiftBy (-j)`;
* `smul_eq_translate`: the action of `ofAdd j` is `translate K j` of
  `GroupApproximation.Pestov91.SubshiftAlgebra`, so `ofAdd j • coord K i = coord K (i - j)`;
* `WitnessRing`: the ring, in `Type`, as the EJZ theorem requires;
* `adjoin_translates_coord_zero`: the translates of `coord (ZMod 2) 0` generate `LC(X, 𝔽₂)` as an
  `𝔽₂`-algebra, from `adjoin_range_coord`;
* `witnessRing_isFinitelyGeneratedRing`: `WitnessRing` is a finitely generated ring.  The
  generators are `C (coord (ZMod 2) 0)`, `u` and `u⁻¹`.
-/

namespace GroupApproximation
namespace Pestov91

open Multiplicative (ofAdd toAdd)

/-- `ℤ` acts on `LocallyConstant X K` by translation: `ofAdd j` sends `f` to `f ∘ shiftBy (-j)`. -/
noncomputable instance witnessAction (K : Type*) [Semiring K] :
    MulSemiringAction (Multiplicative ℤ) (LocallyConstant X K) where
  smul j f :=
    LocallyConstant.comap ⟨shiftBy (-toAdd j), (shiftBy (-toAdd j)).continuous⟩ f
  one_smul f := LocallyConstant.ext fun x => by
    show f (shiftBy (-toAdd (1 : Multiplicative ℤ)) x) = f x
    rw [toAdd_one, neg_zero, shiftBy_zero]
  mul_smul m n f := LocallyConstant.ext fun x => by
    show f (shiftBy (-toAdd (m * n)) x) = f (shiftBy (-toAdd n) (shiftBy (-toAdd m) x))
    rw [toAdd_mul, neg_add_rev, shiftBy_add]
  smul_zero _ := LocallyConstant.ext fun _ => rfl
  smul_add _ _ _ := LocallyConstant.ext fun _ => rfl
  smul_one _ := LocallyConstant.ext fun _ => rfl
  smul_mul _ _ _ := LocallyConstant.ext fun _ => rfl

theorem witnessAction_apply {K : Type*} [Semiring K] (j : ℤ) (f : LocallyConstant X K) (x : X) :
    (ofAdd j • f) x = f (shiftBy (-j) x) :=
  rfl

theorem smul_eq_translate (K : Type*) [CommRing K] (j : ℤ) (f : LocallyConstant X K) :
    ofAdd j • f = translate K j f :=
  LocallyConstant.ext fun _ => rfl

theorem smul_coord (K : Type*) [CommRing K] (j i : ℤ) :
    ofAdd j • coord K i = coord K (i - j) := by
  rw [smul_eq_translate, translate_coord]

/-- **The witness ring** `LC(X, 𝔽₂) ⋊ ℤ` of Pestov 9.1. -/
abbrev WitnessRing : Type :=
  SkewMonoidAlgebra (LocallyConstant X (ZMod 2)) (Multiplicative ℤ)

/-- The translates of `coord (ZMod 2) 0` generate `LC(X, 𝔽₂)` as an `𝔽₂`-algebra. -/
theorem adjoin_translates_coord_zero :
    Algebra.adjoin (ZMod 2) {a : LocallyConstant X (ZMod 2) |
      ∃ j : ℤ, ∃ b ∈ ({coord (ZMod 2) 0} : Finset (LocallyConstant X (ZMod 2))),
        ofAdd j • b = a} = ⊤ :=
  eq_top_iff.2 <| (adjoin_range_coord (ZMod 2)).ge.trans <| Algebra.adjoin_mono <| by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, coord (ZMod 2) 0, Finset.mem_singleton_self _, by
      rw [smul_coord, zero_sub, neg_neg]⟩

/-- **`LC(X, 𝔽₂) ⋊ ℤ` is a finitely generated ring**, with generators `C (coord (ZMod 2) 0)`,
`u` and `u⁻¹`. -/
theorem witnessRing_isFinitelyGeneratedRing : IsFinitelyGeneratedRing WitnessRing :=
  CrossedProduct.isFinitelyGeneratedRing_of_adjoin_translates (isFinitelyGeneratedRing_zmod 2)
    {coord (ZMod 2) 0} adjoin_translates_coord_zero

end Pestov91
end GroupApproximation
