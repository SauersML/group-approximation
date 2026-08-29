import Mathlib.GroupTheory.SemidirectProduct

/-!
# Re-associating an iterated semidirect product

The witness group is built as `A ⋊ (B ⋊ Z)`: Clifford lamps over the coset
space, acted on by the telescope extended by the shift.  Every permanence
theorem for the top layer wants the opposite bracketing, `(A ⋊ B) ⋊ Z`, so
that `Z` is a quotient with a normal kernel `A ⋊ B`.

The two are isomorphic, by the identity map on triples.  The only content is
that the inner action of `B` and the action of `Z` assemble: conjugation by
`inr z` preserves the copy of `A ⋊ B`, because `inr z * inl b = inl (g z b) *
inr z` inside `B ⋊ Z`.
-/

namespace GroupApproximation
namespace SemidirectAssoc

open SemidirectProduct

variable {A B Z : Type*} [Group A] [Group B] [Group Z]
  (g : Z →* MulAut B) (f : (B ⋊[g] Z) →* MulAut A)

/-- The action of the inner base factor on `A`. -/
abbrev baseAction : B →* MulAut A := f.comp (inl : B →* B ⋊[g] Z)

theorem inr_mul_inl (z : Z) (b : B) :
    (inr z : B ⋊[g] Z) * inl b = inl (g z b) * inr z := by
  rw [inl_aut, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

/-- Conjugation by the shift, transported to the inner semidirect product. -/
def outerAction : Z →* MulAut (A ⋊[baseAction g f] B) where
  toFun z :=
    { toFun := fun p ↦ ⟨f (inr z) p.left, g z p.right⟩
      invFun := fun p ↦ ⟨f (inr z⁻¹) p.left, g z⁻¹ p.right⟩
      left_inv := by
        intro p
        apply SemidirectProduct.ext
        · show f (inr z⁻¹) (f (inr z) p.left) = p.left
          rw [← MulAut.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel,
            map_one, map_one]
          rfl
        · show g z⁻¹ (g z p.right) = p.right
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
      right_inv := by
        intro p
        apply SemidirectProduct.ext
        · show f (inr z) (f (inr z⁻¹) p.left) = p.left
          rw [← MulAut.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel,
            map_one, map_one]
          rfl
        · show g z (g z⁻¹ p.right) = p.right
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          rfl
      map_mul' := by
        intro p q
        apply SemidirectProduct.ext
        · show f (inr z) (p.left * baseAction g f p.right q.left) =
            f (inr z) p.left * baseAction g f (g z p.right) (f (inr z) q.left)
          rw [map_mul]
          congr 1
          show f (inr z) (f (inl p.right) q.left) =
            f (inl (g z p.right)) (f (inr z) q.left)
          rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul,
            inr_mul_inl]
        · show g z (p.right * q.right) = g z p.right * g z q.right
          exact map_mul _ _ _ }
  map_one' := by
    apply MulEquiv.ext
    intro p
    apply SemidirectProduct.ext
    · show f (inr (1 : Z)) p.left = p.left
      rw [map_one, map_one]
      rfl
    · show g (1 : Z) p.right = p.right
      rw [map_one]
      rfl
  map_mul' z z' := by
    apply MulEquiv.ext
    intro p
    apply SemidirectProduct.ext
    · show f (inr (z * z')) p.left = f (inr z) (f (inr z') p.left)
      rw [map_mul, map_mul, MulAut.mul_apply]
    · show g (z * z') p.right = g z (g z' p.right)
      rw [map_mul, MulAut.mul_apply]

/-- **Re-association**: `(A ⋊ B) ⋊ Z ≃* A ⋊ (B ⋊ Z)`. -/
def assocEquiv :
    ((A ⋊[baseAction g f] B) ⋊[outerAction g f] Z) ≃* (A ⋊[f] (B ⋊[g] Z)) where
  toFun p := ⟨p.left.left, ⟨p.left.right, p.right⟩⟩
  invFun q := ⟨⟨q.left, q.right.left⟩, q.right.right⟩
  left_inv p := rfl
  right_inv q := rfl
  map_mul' p q := by
    apply SemidirectProduct.ext
    · show p.left.left * f (inl p.left.right) (f (inr p.right) q.left.left) =
        p.left.left * f (⟨p.left.right, p.right⟩ : B ⋊[g] Z) q.left.left
      congr 1
      have hsplit : (⟨p.left.right, p.right⟩ : B ⋊[g] Z) =
          inl p.left.right * inr p.right :=
        (inl_left_mul_inr_right _).symm
      rw [hsplit, map_mul, MulAut.mul_apply]
    · apply SemidirectProduct.ext
      · show p.left.right * g p.right q.left.right =
          p.left.right * g p.right q.left.right
        rfl
      · show p.right * q.right = p.right * q.right
        rfl

end SemidirectAssoc
end GroupApproximation
