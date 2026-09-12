import GroupApproximation.Kazhdan.FreeGroupFoxHomotopy
import GroupApproximation.Meta.AxiomGuard

/-!
# Fox calculus on the free group, and pushforward along a quotient

The calculus the relation sequence needs:

* the prefix of an integral Fox boundary is a left translation (`foxFrom_initial`);
* on `F = F(X)` the Fox derivative is a crossed homomorphism
  `∂(gh) = ∂g + g·∂h` (`foxFree_mul`), with `∂1 = 0` and `∂(g⁻¹) = −g⁻¹·∂g`, and its boundary
  is `[g] − [1]` (`foxD₁_foxFree`);
* the pushforward `mapG φ : ℤF^ι → ℤG^ι` along a group homomorphism is equivariant
  (`mapG_act`) and natural for `∂₁` (`mapG_foxD₁`).
-/

namespace GroupApproximation.FoxComplex

open FreeResolutionPrimeOrder FoxBoundary PresentedGroupRelatorReplay

universe u v w

section Initial

variable {G : Type u} [Group G] {X : Type v}

/-- **The prefix is a translation**: `foxFrom s p w = p · foxFrom s 1 w`. -/
theorem foxFrom_initial (s : X → G) (initial : G) (w : SignedWord X) :
    foxFrom s initial w = act initial (foxFrom s 1 w) := by
  induction w generalizing initial with
  | nil => rw [foxFrom_nil, foxFrom_nil, map_zero]
  | cons letter rest ih =>
      rcases letter with ⟨x, _ | _⟩
      · rw [foxFrom_cons_false, foxFrom_cons_false, ih (initial * (s x)⁻¹), ih (1 * (s x)⁻¹),
          map_add, map_neg, act_single, act_act, one_mul]
      · rw [foxFrom_cons_true, foxFrom_cons_true, ih (initial * s x), ih (1 * s x), map_add,
          act_single, act_act, one_mul, mul_one]

end Initial

section FreeGroupCalculus

variable {X : Type v}

theorem foxFree_eq_act (p g : FreeGroup X) : foxFree p g = act p (foxFree 1 g) := by
  induction g using Quot.ind with
  | mk w => exact foxFrom_initial FreeGroup.of p w

theorem foxFree_one (p : FreeGroup X) : foxFree p 1 = 0 := rfl

/-- **The Fox derivative is a crossed homomorphism**: `∂(gh) = ∂g + g·∂h`. -/
theorem foxFree_mul (g h : FreeGroup X) :
    foxFree 1 (g * h) = foxFree 1 g + act g (foxFree 1 h) := by
  induction g using Quot.ind with
  | mk w₁ =>
      induction h using Quot.ind with
      | mk w₂ =>
          show foxFree 1 (FreeGroup.mk w₁ * FreeGroup.mk w₂) =
            foxFree 1 (FreeGroup.mk w₁) + act (FreeGroup.mk w₁) (foxFree 1 (FreeGroup.mk w₂))
          rw [FreeGroup.mul_mk, foxFree_mk, foxFree_mk, foxFree_mk, foxFrom_append, one_mul,
            wordValue_of, foxFrom_initial FreeGroup.of (FreeGroup.mk w₁) w₂]

theorem foxFree_inv (g : FreeGroup X) : foxFree 1 g⁻¹ = -act g⁻¹ (foxFree 1 g) := by
  have h := foxFree_mul g⁻¹ g
  rw [inv_mul_cancel, foxFree_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The boundary of the Fox derivative: `∂₁ (∂g) = [g] − [1]`. -/
theorem foxD₁_foxFree (g : FreeGroup X) :
    foxD₁ FreeGroup.of (foxFree 1 g) =
      Finsupp.single ((), g) 1 - Finsupp.single ((), (1 : FreeGroup X)) 1 := by
  induction g using Quot.ind with
  | mk w =>
      show foxD₁ FreeGroup.of (foxFrom FreeGroup.of 1 w) =
        Finsupp.single ((), FreeGroup.mk w) 1 - Finsupp.single ((), (1 : FreeGroup X)) 1
      rw [foxD₁_foxFrom, one_mul, wordValue_of]

end FreeGroupCalculus

section Pushforward

variable {F : Type u} [Group F] {G : Type v} [Group G]

/-- Pushforward of free modules along a group homomorphism. -/
noncomputable def mapG {ι : Type w} (φ : F →* G) : FreeZG F ι →+ FreeZG G ι :=
  Finsupp.mapDomain.addMonoidHom (Prod.map id φ)

theorem mapG_single {ι : Type w} (φ : F →* G) (i : ι) (g : F) (c : ℤ) :
    mapG φ (Finsupp.single (i, g) c) = Finsupp.single (i, φ g) c := by
  show Finsupp.mapDomain (Prod.map id φ) (Finsupp.single (i, g) c) = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem mapG_act {ι : Type w} (φ : F →* G) (g : F) (f : FreeZG F ι) :
    mapG φ (act g f) = act (φ g) (mapG φ f) := by
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · rw [map_zero, map_zero, map_zero]
  · intro f f' hf hf'
    rw [map_add, map_add, hf, hf', map_add]
  · rintro ⟨i, h⟩ c
    rw [act_single, mapG_single, mapG_single, act_single, map_mul]

/-- **Naturality of `∂₁`** under pushforward. -/
theorem mapG_foxD₁ {X : Type w} (φ : F →* G) (s : X → F) (f : FreeZG F X) :
    mapG φ (foxD₁ s f) = foxD₁ (fun x ↦ φ (s x)) (mapG φ f) := by
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · rw [map_zero, map_zero, map_zero, map_zero]
  · intro f f' hf hf'
    rw [map_add, map_add, hf, hf', map_add, map_add]
  · rintro ⟨x, h⟩ c
    rw [foxD₁_single, map_zsmul, map_sub, mapG_single, mapG_single, mapG_single, foxD₁_single,
      map_mul]

end Pushforward

end GroupApproximation.FoxComplex

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.FoxComplex.foxFrom_initial
#audit_axioms GroupApproximation.FoxComplex.foxFree_mul
#audit_axioms GroupApproximation.FoxComplex.foxFree_inv
#audit_axioms GroupApproximation.FoxComplex.foxD₁_foxFree
#audit_axioms GroupApproximation.FoxComplex.mapG_act
#audit_axioms GroupApproximation.FoxComplex.mapG_foxD₁
