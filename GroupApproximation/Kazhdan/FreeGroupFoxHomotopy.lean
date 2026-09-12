import GroupApproximation.Kazhdan.FoxComplexZ
import GroupApproximation.Meta.AxiomGuard

/-!
# The augmentation ideal of a free group is free

For the free group `F = F(X)` with generator values `of`, the integral Fox boundary of a signed
word depends only on the group element it represents (`foxFrom_step`): cancelling a pair
`x x⁻¹` contributes `[(x, p)] − [(x, p)] = 0`.  So it descends to the **Fox derivative**
`foxFree : F → ℤF^X`, a crossed homomorphism (`foxFree_mul_of`).  The additive map
`h [g] = foxFree g` is a left inverse of `∂₁` (`foxHomotopy_foxD₁`), so `∂₁ : ℤF^X → ℤF` is
injective (`foxD₁_injective_freeGroup`): the augmentation ideal of `ℤF` is free on the
`x − 1`.  This is the input to the relation sequence of a presentation.
-/

namespace GroupApproximation.FoxComplex

open FreeResolutionPrimeOrder FoxBoundary PresentedGroupRelatorReplay

universe u v

section Cocycle

variable {G : Type u} [Group G] {X : Type v}

/-- **The append cocycle** of integral Fox boundaries. -/
theorem foxFrom_append (s : X → G) (initial : G) (w₁ w₂ : SignedWord X) :
    foxFrom s initial (w₁ ++ w₂) =
      foxFrom s initial w₁ + foxFrom s (initial * wordValue s w₁) w₂ := by
  induction w₁ generalizing initial with
  | nil => rw [List.nil_append, foxFrom_nil, zero_add, wordValue_nil, mul_one]
  | cons letter rest ih =>
      rcases letter with ⟨x, _ | _⟩
      · rw [List.cons_append, foxFrom_cons_false, foxFrom_cons_false, ih, wordValue_cons,
          letterValue_false, mul_assoc, add_assoc]
      · rw [List.cons_append, foxFrom_cons_true, foxFrom_cons_true, ih, wordValue_cons,
          letterValue_true, mul_assoc, add_assoc]

end Cocycle

variable {X : Type v}

theorem wordValue_of (w : SignedWord X) :
    wordValue (FreeGroup.of : X → FreeGroup X) w = FreeGroup.mk w :=
  wordValue_freeGroup_map (MonoidHom.id (FreeGroup X)) w

/-- Integral Fox boundaries over the free group are invariant under one reduction step. -/
theorem foxFrom_step (initial : FreeGroup X) {L₁ L₂ : SignedWord X}
    (h : FreeGroup.Red.Step L₁ L₂) :
    foxFrom FreeGroup.of initial L₁ = foxFrom FreeGroup.of initial L₂ := by
  cases h with
  | @not L₁ L₂ x b =>
      rw [foxFrom_append, foxFrom_append]
      congr 1
      generalize initial * wordValue FreeGroup.of L₁ = p
      cases b
      · try simp only [Bool.not_false]
        rw [foxFrom_cons_false, foxFrom_cons_true, inv_mul_cancel_right, neg_add_cancel_left]
      · try simp only [Bool.not_true]
        rw [foxFrom_cons_true, foxFrom_cons_false, mul_inv_cancel_right, add_neg_cancel_left]

/-- **The Fox derivative** on the free group, after a prefix `p`. -/
noncomputable def foxFree (p : FreeGroup X) : FreeGroup X → FreeZG (FreeGroup X) X :=
  Quot.lift (foxFrom FreeGroup.of p) fun _ _ h ↦ foxFrom_step p h

theorem foxFree_mk (p : FreeGroup X) (w : SignedWord X) :
    foxFree p (FreeGroup.mk w) = foxFrom FreeGroup.of p w := rfl

/-- **The crossed-homomorphism identity** on a generator. -/
theorem foxFree_mul_of (p g : FreeGroup X) (x : X) :
    foxFree p (g * FreeGroup.of x) = foxFree p g + Finsupp.single (x, p * g) 1 := by
  induction g using Quot.ind with
  | mk w =>
      show foxFree p (FreeGroup.mk w * FreeGroup.mk [(x, true)]) =
        foxFree p (FreeGroup.mk w) + Finsupp.single (x, p * FreeGroup.mk w) 1
      rw [FreeGroup.mul_mk, foxFree_mk, foxFree_mk, foxFrom_append, foxFrom_cons_true,
        foxFrom_nil, add_zero, wordValue_of]

/-- The contracting homotopy `h [g] = ∂ g`. -/
noncomputable def foxHomotopy : FreeZG (FreeGroup X) Unit →+ FreeZG (FreeGroup X) X :=
  Finsupp.liftAddHom fun q ↦ zmultiplesHom (FreeZG (FreeGroup X) X) (foxFree 1 q.2)

theorem foxHomotopy_single (g : FreeGroup X) (c : ℤ) :
    foxHomotopy (Finsupp.single ((), g) c) = c • foxFree (1 : FreeGroup X) g := by
  simp only [foxHomotopy, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]

/-- **The homotopy splits `∂₁`**: `h ∘ ∂₁ = id` over a free group. -/
theorem foxHomotopy_foxD₁ (f : FreeZG (FreeGroup X) X) :
    foxHomotopy (foxD₁ FreeGroup.of f) = f := by
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · rw [map_zero, map_zero]
  · intro f f' hf hf'
    rw [map_add, map_add, hf, hf']
  · rintro ⟨x, g⟩ c
    rw [foxD₁_single, map_zsmul, map_sub, foxHomotopy_single, foxHomotopy_single, one_zsmul,
      one_zsmul, foxFree_mul_of, one_mul, add_sub_cancel_left, Finsupp.smul_single_one]

/-- **The augmentation ideal of a free group is free on the `x − 1`**: `∂₁ : ℤF^X → ℤF` is
injective. -/
theorem foxD₁_injective_freeGroup :
    Function.Injective (foxD₁ (FreeGroup.of : X → FreeGroup X)) :=
  Function.LeftInverse.injective foxHomotopy_foxD₁

end GroupApproximation.FoxComplex

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.FoxComplex.foxFrom_append
#audit_axioms GroupApproximation.FoxComplex.foxFrom_step
#audit_axioms GroupApproximation.FoxComplex.foxFree_mul_of
#audit_axioms GroupApproximation.FoxComplex.foxHomotopy_foxD₁
#audit_axioms GroupApproximation.FoxComplex.foxD₁_injective_freeGroup
