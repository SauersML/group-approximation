import GroupApproximation.Kazhdan.FoxBoundary
import GroupApproximation.Algebra.FreeResolutionPrimeOrder
import GroupApproximation.Meta.AxiomGuard

/-!
# The integral Fox complex of a presentation

For generator values `s : X → G` and relators `rel : ρ → SignedWord X`, the Fox complex

`ℤG^ρ →∂₂ ℤG^X →∂₁ ℤG →ε ℤ → 0`

written concretely on the free modules of `Algebra/FreeResolutionPrimeOrder.lean`
(`FreeZG G ι = ι × G →₀ ℤ`, with `act` translating the group coordinate):

* `∂₁ (x, g) = g·s(x) − g` (`foxD₁`),
* `∂₂ (r, g) = g · ∂(rel r)`, where `∂ w = foxZ s w` is the integral Fox boundary of a signed
  word (`foxD₂`),
* `ε (q) = 1` on every basis vector (`augZ`).

All three maps are equivariant.  The Fox telescoping identity
`∂₁ (foxZ s w) = [wordValue s w] − [1]` (`foxD₁_foxZ`) is the integral form of
`FoxBoundary.sum_boundary_mul_coboundary`.  It gives `ε ∘ ∂₁ = 0` and, when every relator
evaluates to `1`, `∂₁ ∘ ∂₂ = 0`.
-/

namespace GroupApproximation.FoxComplex

open FreeResolutionPrimeOrder FoxBoundary PresentedGroupRelatorReplay

universe u v w

variable {G : Type u} [Group G]

/-- Translation of a basis vector. -/
theorem act_single {ι : Type v} (g : G) (i : ι) (h : G) (c : ℤ) :
    act g (Finsupp.single (i, h) c) = Finsupp.single (i, g * h) c := by
  show Finsupp.equivMapDomain (shiftEquiv g) (Finsupp.single (i, h) c) = _
  rw [Finsupp.equivMapDomain_single]
  rfl

/-! ### The augmentation -/

/-- The augmentation `ε : ℤG^ι → ℤ`, summing all coefficients. -/
noncomputable def augZ {ι : Type v} : FreeZG G ι →+ ℤ :=
  Finsupp.liftAddHom fun _ ↦ AddMonoidHom.id ℤ

theorem augZ_single {ι : Type v} (q : ι × G) (c : ℤ) :
    augZ (Finsupp.single q c : FreeZG G ι) = c := by
  simp only [augZ, Finsupp.liftAddHom_apply_single, AddMonoidHom.id_apply]

theorem augZ_act {ι : Type v} (g : G) (f : FreeZG G ι) : augZ (act g f) = augZ f := by
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · rw [map_zero, map_zero]
  · intro f f' hf hf'
    rw [map_add, map_add, hf, hf']
  · rintro ⟨i, h⟩ c
    rw [act_single, augZ_single, augZ_single]

/-! ### Integral Fox boundaries of signed words -/

variable {X : Type v}

theorem letterValue_true (s : X → G) (x : X) : letterValue s (x, true) = s x := rfl

theorem letterValue_false (s : X → G) (x : X) : letterValue s (x, false) = (s x)⁻¹ := rfl

theorem wordValue_nil (s : X → G) : wordValue s [] = 1 := rfl

theorem wordValue_cons (s : X → G) (letter : X × Bool) (rest : SignedWord X) :
    wordValue s (letter :: rest) = letterValue s letter * wordValue s rest := by
  simp only [wordValue, List.map_cons, List.prod_cons]

/-- The integral Fox boundary of a signed word after a traversed prefix: a positive letter
`x` at prefix `p` contributes the basis vector `(x, p)`, an inverse letter contributes minus
the basis vector at the new prefix. -/
noncomputable def foxFrom (s : X → G) : G → SignedWord X → FreeZG G X
  | _, [] => 0
  | initial, (x, positive) :: rest =>
      (if positive then Finsupp.single (x, initial) 1
        else -Finsupp.single (x, initial * letterValue s (x, positive)) 1) +
      foxFrom s (initial * letterValue s (x, positive)) rest

theorem foxFrom_nil (s : X → G) (initial : G) : foxFrom s initial [] = 0 := rfl

theorem foxFrom_cons_true (s : X → G) (initial : G) (x : X) (rest : SignedWord X) :
    foxFrom s initial ((x, true) :: rest) =
      Finsupp.single (x, initial) 1 + foxFrom s (initial * s x) rest := rfl

theorem foxFrom_cons_false (s : X → G) (initial : G) (x : X) (rest : SignedWord X) :
    foxFrom s initial ((x, false) :: rest) =
      -Finsupp.single (x, initial * (s x)⁻¹) 1 + foxFrom s (initial * (s x)⁻¹) rest := rfl

/-- The integral Fox boundary of a signed word. -/
noncomputable def foxZ (s : X → G) (w : SignedWord X) : FreeZG G X :=
  foxFrom s 1 w

/-! ### The boundary maps -/

/-- `∂₁ (x, g) = g·s(x) − g`. -/
noncomputable def foxD₁ (s : X → G) : FreeZG G X →+ FreeZG G Unit :=
  Finsupp.liftAddHom fun q ↦
    zmultiplesHom (FreeZG G Unit)
      (Finsupp.single ((), q.2 * s q.1) 1 - Finsupp.single ((), q.2) 1)

theorem foxD₁_single (s : X → G) (x : X) (g : G) (c : ℤ) :
    foxD₁ s (Finsupp.single (x, g) c) =
      c • (Finsupp.single ((), g * s x) 1 - Finsupp.single ((), g) 1) := by
  simp only [foxD₁, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]

/-- **Fox telescoping** with an arbitrary initial prefix. -/
theorem foxD₁_foxFrom (s : X → G) (initial : G) (w : SignedWord X) :
    foxD₁ s (foxFrom s initial w) =
      Finsupp.single ((), initial * wordValue s w) 1 - Finsupp.single ((), initial) 1 := by
  induction w generalizing initial with
  | nil => rw [foxFrom_nil, map_zero, wordValue_nil, mul_one, sub_self]
  | cons letter rest ih =>
      rcases letter with ⟨x, _ | _⟩
      · rw [foxFrom_cons_false, map_add, map_neg, foxD₁_single, ih, wordValue_cons,
          letterValue_false, inv_mul_cancel_right, one_smul, mul_assoc]
        abel
      · rw [foxFrom_cons_true, map_add, foxD₁_single, ih, wordValue_cons, letterValue_true,
          one_smul, mul_assoc]
        abel

/-- **Fox telescoping**: `∂₁ (∂ w) = [w] − [1]`. -/
theorem foxD₁_foxZ (s : X → G) (w : SignedWord X) :
    foxD₁ s (foxZ s w) = Finsupp.single ((), wordValue s w) 1 - Finsupp.single ((), 1) 1 := by
  rw [foxZ, foxD₁_foxFrom, one_mul]

theorem foxD₁_act (s : X → G) (g : G) (f : FreeZG G X) :
    foxD₁ s (act g f) = act g (foxD₁ s f) := by
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · rw [map_zero, map_zero, map_zero]
  · intro f f' hf hf'
    rw [map_add, map_add, hf, hf', map_add]
  · rintro ⟨x, h⟩ c
    rw [act_single, foxD₁_single, foxD₁_single, map_zsmul, map_sub, act_single, act_single,
      mul_assoc]

/-- `ε ∘ ∂₁ = 0`. -/
theorem augZ_foxD₁ (s : X → G) (f : FreeZG G X) : augZ (foxD₁ s f) = 0 := by
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · rw [map_zero, map_zero]
  · intro f f' hf hf'
    rw [map_add, map_add, hf, hf', add_zero]
  · rintro ⟨x, h⟩ c
    rw [foxD₁_single, map_zsmul, map_sub, augZ_single, augZ_single, sub_self, smul_zero]

variable {ρ : Type w}

/-- `∂₂ (r, g) = g · ∂(rel r)`. -/
noncomputable def foxD₂ (s : X → G) (rel : ρ → SignedWord X) : FreeZG G ρ →+ FreeZG G X :=
  Finsupp.liftAddHom fun q ↦ zmultiplesHom (FreeZG G X) (act q.2 (foxZ s (rel q.1)))

theorem foxD₂_single (s : X → G) (rel : ρ → SignedWord X) (r : ρ) (g : G) (c : ℤ) :
    foxD₂ s rel (Finsupp.single (r, g) c) = c • act g (foxZ s (rel r)) := by
  simp only [foxD₂, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]

theorem foxD₂_act (s : X → G) (rel : ρ → SignedWord X) (g : G) (f : FreeZG G ρ) :
    foxD₂ s rel (act g f) = act g (foxD₂ s rel f) := by
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · rw [map_zero, map_zero, map_zero]
  · intro f f' hf hf'
    rw [map_add, map_add, hf, hf', map_add]
  · rintro ⟨r, h⟩ c
    rw [act_single, foxD₂_single, foxD₂_single, map_zsmul, act_act]

/-- `∂₁ ∘ ∂₂ = 0` when every relator evaluates to `1`. -/
theorem foxD₁_foxD₂ (s : X → G) (rel : ρ → SignedWord X)
    (hrel : ∀ r, wordValue s (rel r) = 1) (f : FreeZG G ρ) :
    foxD₁ s (foxD₂ s rel f) = 0 := by
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · rw [map_zero, map_zero]
  · intro f f' hf hf'
    rw [map_add, map_add, hf, hf', add_zero]
  · rintro ⟨r, h⟩ c
    rw [foxD₂_single, map_zsmul, foxD₁_act, foxD₁_foxZ, hrel r, sub_self, map_zero, smul_zero]

end GroupApproximation.FoxComplex

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.FoxComplex.act_single
#audit_axioms GroupApproximation.FoxComplex.augZ_act
#audit_axioms GroupApproximation.FoxComplex.foxD₁_foxFrom
#audit_axioms GroupApproximation.FoxComplex.foxD₁_foxZ
#audit_axioms GroupApproximation.FoxComplex.foxD₁_act
#audit_axioms GroupApproximation.FoxComplex.augZ_foxD₁
#audit_axioms GroupApproximation.FoxComplex.foxD₂_act
#audit_axioms GroupApproximation.FoxComplex.foxD₁_foxD₂
