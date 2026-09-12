import GroupApproximation.Analysis.PowersAveraging
import GroupApproximation.Meta.AxiomGuard

/-!
# Composing two averagings gives one averaging

Averaging an element by `λ(g₁), …, λ(gₙ)` and then averaging the result by
`λ(h₁), …, λ(h_m)` is the same as averaging once, by the `m·n` elements
`hⱼ gᵢ`.  That is the whole content of this module, and it is what makes an
*iterated* averaging argument legitimate: `PowersAveragingEstimate` asks for a
single average, so an argument that kills one obstruction at a time has to know
that the composite is still of the required shape.

## Where this is needed

Powers' condition in its **weak** form only controls finite sets inside a single
conjugacy class.  An element of the group algebra with trace zero has a support
meeting finitely many conjugacy classes, and conjugation preserves conjugacy
classes, so an averaging argument can kill the classes one at a time.  Composing
those steps is legal exactly because of the lemma below, and the norm does not
grow along the way because averaging is a contraction.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra`; certifies no printed sentence on
its own.
-/

namespace GroupApproximation
namespace ReducedGroupCStarTrace

universe u

noncomputable section

variable (G : Type u) [Group G]

/-- Conjugating by `λ(h)` after conjugating by `λ(g)` is conjugating by
`λ(h g)`. -/
theorem conj_reducedLeftRegular_comp (a : ReducedGroupCStar G) (g h : G) :
    reducedLeftRegular G h *
        (reducedLeftRegular G g * a * star (reducedLeftRegular G g)) *
        star (reducedLeftRegular G h)
      = reducedLeftRegular G (h * g) * a * star (reducedLeftRegular G (h * g)) := by
  simp only [reducedLeftRegular_mul, star_mul, star_reducedLeftRegular, mul_assoc]

/-- The family that averages twice at once: `hⱼ gᵢ`, indexed by `Fin (m · n)`.

It must not depend on the element being averaged, because the induction that
consumes it needs **one** family that works for a whole finite list of
elements. -/
def composeFamily {n m : ℕ} (g : Fin n → G) (h : Fin m → G) : Fin (m * n) → G :=
  fun l ↦ h (finProdFinEquiv.symm l).1 * g (finProdFinEquiv.symm l).2

/-- **The composition of two averagings is an averaging**, over
`composeFamily`. -/
theorem reducedAverage_comp (a : ReducedGroupCStar G) {n m : ℕ}
    (g : Fin n → G) (h : Fin m → G) :
    ((m : ℂ)⁻¹ • ∑ j : Fin m, reducedLeftRegular G (h j) *
        ((n : ℂ)⁻¹ • ∑ i : Fin n,
          reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i))) *
        star (reducedLeftRegular G (h j)))
      = ((m * n : ℕ) : ℂ)⁻¹ • ∑ l : Fin (m * n),
          reducedLeftRegular G (composeFamily G g h l) * a *
            star (reducedLeftRegular G (composeFamily G g h l)) := by
  classical
  have hstep : ∀ j : Fin m,
      reducedLeftRegular G (h j) *
          ((n : ℂ)⁻¹ • ∑ i : Fin n,
            reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i))) *
          star (reducedLeftRegular G (h j))
        = (n : ℂ)⁻¹ • ∑ i : Fin n,
            reducedLeftRegular G (h j * g i) * a *
              star (reducedLeftRegular G (h j * g i)) := by
    intro j
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ conj_reducedLeftRegular_comp G a (g i) (h j)
  have hreindex : (∑ j : Fin m, ∑ i : Fin n,
      reducedLeftRegular G (h j * g i) * a * star (reducedLeftRegular G (h j * g i)))
      = ∑ l : Fin (m * n),
          reducedLeftRegular G (composeFamily G g h l) * a *
            star (reducedLeftRegular G (composeFamily G g h l)) := by
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv finProdFinEquiv _ _ fun x ↦ by
      simp only [composeFamily, Equiv.symm_apply_apply]
  have hcast : ((m : ℂ)⁻¹ * (n : ℂ)⁻¹) = ((m * n : ℕ) : ℂ)⁻¹ := by
    rw [Nat.cast_mul, mul_inv]
  rw [Finset.sum_congr rfl fun j _ ↦ hstep j, ← Finset.smul_sum, smul_smul, hcast,
    hreindex]

/-! ## Averaging preserves a conjugacy class -/

/-- Conjugating a translation by a canonical unitary translates by a conjugate:
`λ(g) λ(γ) λ(g)⋆ = λ(g γ g⁻¹)`. -/
theorem conj_reducedLeftRegular (g γ : G) :
    reducedLeftRegular G g * reducedLeftRegular G γ * star (reducedLeftRegular G g)
      = reducedLeftRegular G (g * γ * g⁻¹) := by
  simp only [star_reducedLeftRegular, reducedLeftRegular_mul, mul_assoc]

/-- The coefficients occurring in an average of `∑ⱼ cⱼ λ(γⱼ)`: each is `cⱼ/n`,
so it vanishes wherever `cⱼ` does. -/
def conjAverageCoeff {m : ℕ} (c : Fin m → ℂ) (n : ℕ) : Fin (n * m) → ℂ :=
  fun l ↦ (n : ℂ)⁻¹ * c (finProdFinEquiv.symm l).2

/-- The translations occurring in an average of `∑ⱼ cⱼ λ(γⱼ)`: each is by a
conjugate `gᵢ γⱼ gᵢ⁻¹` of one of the original elements. -/
def conjAverageFamily {m n : ℕ} (γ : Fin m → G) (g : Fin n → G) : Fin (n * m) → G :=
  fun l ↦ g (finProdFinEquiv.symm l).1 * γ (finProdFinEquiv.symm l).2 *
    (g (finProdFinEquiv.symm l).1)⁻¹

theorem conjAverageFamily_conj {m n : ℕ} (γ : Fin m → G) (g : Fin n → G)
    (l : Fin (n * m)) :
    conjAverageFamily G γ g l
      = g (finProdFinEquiv.symm l).1 * γ (finProdFinEquiv.symm l).2 *
        (g (finProdFinEquiv.symm l).1)⁻¹ := rfl

theorem conjAverageCoeff_apply {m : ℕ} (c : Fin m → ℂ) (n : ℕ) (l : Fin (n * m)) :
    conjAverageCoeff c n l = (n : ℂ)⁻¹ * c (finProdFinEquiv.symm l).2 := rfl

/-- **Averaging a combination of translations by members of one conjugacy class
gives another such combination.**

Every translation occurring in the average is by a conjugate of one of the
original elements, and every coefficient is a multiple of an original one, so a
hypothesis confining the support to a single conjugacy class survives averaging.
That is what lets an averaging argument treat the conjugacy classes of a
finitely supported element one at a time. -/
theorem average_conjTranslationSum {m : ℕ} (c : Fin m → ℂ) (γ : Fin m → G)
    {n : ℕ} (g : Fin n → G) :
    ((n : ℂ)⁻¹ • ∑ i : Fin n, reducedLeftRegular G (g i) *
        (∑ j : Fin m, c j • reducedLeftRegular G (γ j)) *
        star (reducedLeftRegular G (g i)))
      = ∑ l : Fin (n * m),
          conjAverageCoeff c n l • reducedLeftRegular G (conjAverageFamily G γ g l) := by
  classical
  have hstep : ∀ i : Fin n,
      reducedLeftRegular G (g i) *
          (∑ j : Fin m, c j • reducedLeftRegular G (γ j)) *
          star (reducedLeftRegular G (g i))
        = ∑ j : Fin m, c j • reducedLeftRegular G (g i * γ j * (g i)⁻¹) := by
    intro i
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_smul_comm, smul_mul_assoc, conj_reducedLeftRegular]
  have hinner : ∀ i : Fin n,
      ((n : ℂ)⁻¹ • ∑ j : Fin m, c j • reducedLeftRegular G (g i * γ j * (g i)⁻¹))
        = ∑ j : Fin m,
            ((n : ℂ)⁻¹ * c j) • reducedLeftRegular G (g i * γ j * (g i)⁻¹) := by
    intro i
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [smul_smul]
  rw [Finset.sum_congr rfl fun i _ ↦ hstep i, Finset.smul_sum,
    Finset.sum_congr rfl fun i _ ↦ hinner i, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv finProdFinEquiv _ _ fun x ↦ by
    simp only [conjAverageCoeff, conjAverageFamily, Equiv.symm_apply_apply]

end

end ReducedGroupCStarTrace
end GroupApproximation

open GroupApproximation.ReducedGroupCStarTrace

#audit_axioms conj_reducedLeftRegular_comp
#audit_axioms composeFamily
#audit_axioms reducedAverage_comp
#audit_axioms conj_reducedLeftRegular
#audit_axioms conjAverageCoeff
#audit_axioms conjAverageFamily
#audit_axioms average_conjTranslationSum
