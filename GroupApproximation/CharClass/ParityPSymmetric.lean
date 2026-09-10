import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import GroupApproximation.CharClass.ParityPData

/-!
# The `e`-expansion of a symmetric polynomial, and its linear coefficient

This is the infrastructure half of `sp-design`'s L4a.  The mathematical content of L4a is
the *value* of one integer; everything here is the statement that the value is well
defined, and that "modulo decomposables" can be read off a single coefficient.

`MvPolynomial.esymmAlgEquiv` — the fundamental theorem of symmetric polynomials, in Mathlib
— says that when `Fintype.card σ = n` the algebra map `X i ↦ e_{i+1}` is an isomorphism
`R[X_0,…,X_{n-1}] ≃ₐ[R] Λ_σ`.  So every symmetric polynomial has a unique `e`-expansion,
and the coefficient of the **linear** monomial `X_{N-1}` in that expansion is exactly "the
coefficient of `e_N` modulo decomposables".

**No quotient ring is built.**  The functional is a coefficient, and it kills a product of
two `e`'s of positive index for the reason that a product of two elements with vanishing
constant term has vanishing linear part.  That last step is done in the dual numbers
`DualNumber R = TrivSqZeroExt R R`, where it is one application of
`TrivSqZeroExt.snd_mul`: no antidiagonal of a `Finsupp`, no ideal, no grading.

## Where this is going

`ParityPWuCartan.lean` computes `P^i(e_{i+1}(y)) = κ^i · m_{(p^i,1)}(y)`.  What remains of
L4a is the value of `eCoeff` on `m_{(p^i,1)}`, which is `(−1)^{i(p−1)}·(1 + p·i)` by
Newton's identities (`MvPolynomial.psum_eq_mul_esymm_sub_sum`, whose subtracted sum is a
sum of products of two positive-weight symmetric polynomials and is therefore killed by
`eCoeff`), plus the fact that a weight-`N`-homogeneous symmetric polynomial is
`eCoeff·e_N` plus decomposables.

## Main results

* `GroupApproximation.CharClass.ParityP.eExpand` — the `e`-expansion.
* `ParityP.eCoeff` — the coefficient of one `e` in it.
* `ParityP.eCoeff_esymmSub_self` — `eCoeff j (e_{j+1}) = 1`.
* `ParityP.eCoeff_mul_eq_zero` — the coefficient kills a product of two symmetric
  polynomials whose `e`-expansions have vanishing constant term.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

namespace ParityP

open MvPolynomial

section EExpand

variable {R : Type*} [CommRing R] {n : ℕ}

/-- `e_a`, as an element of the symmetric subalgebra of `R[X_0,…,X_{n-1}]`. -/
noncomputable def esymmSub (R : Type*) [CommRing R] (n a : ℕ) :
    symmetricSubalgebra (Fin n) R :=
  ⟨esymm (Fin n) R a, esymm_isSymmetric (Fin n) R a⟩

/-- The `e`-expansion of a symmetric polynomial: its unique preimage under the algebra map
`X i ↦ e_{i+1}`, which is an isomorphism by the fundamental theorem of symmetric
polynomials. -/
noncomputable def eExpand (f : symmetricSubalgebra (Fin n) R) : MvPolynomial (Fin n) R :=
  (esymmAlgEquiv (Fin n) R (Fintype.card_fin n)).symm f

theorem eExpand_esymmSub (k : Fin n) : eExpand (esymmSub R n ((k : ℕ) + 1)) = X k :=
  esymmAlgEquiv_symm_apply ..

theorem eExpand_mul (f g : symmetricSubalgebra (Fin n) R) :
    eExpand (f * g) = eExpand f * eExpand g :=
  map_mul _ f g

theorem eExpand_add (f g : symmetricSubalgebra (Fin n) R) :
    eExpand (f + g) = eExpand f + eExpand g :=
  map_add _ f g

theorem eExpand_neg (f : symmetricSubalgebra (Fin n) R) : eExpand (-f) = -eExpand f :=
  map_neg _ f

theorem eExpand_zero : eExpand (0 : symmetricSubalgebra (Fin n) R) = 0 := map_zero _

/-! ### The linear coefficient, through the dual numbers -/

/-- The dual-number evaluation that reads off the coefficient of `X j`: send `X j` to `ε`
and every other variable to `0`.  A polynomial's image is `(constant term) + (coefficient
of `X j`)·ε`, because every monomial of degree at least two contains `ε²  = 0`. -/
noncomputable def eLin (j : Fin n) (f : symmetricSubalgebra (Fin n) R) : DualNumber R :=
  aeval (fun k => if k = j then (DualNumber.eps : DualNumber R) else 0) (eExpand f)

/-- The coefficient of `e_{j+1}` in the `e`-expansion, i.e. the coefficient of `e_{j+1}`
modulo decomposables. -/
noncomputable def eCoeff (j : Fin n) (f : symmetricSubalgebra (Fin n) R) : R :=
  (eLin j f).snd

theorem eLin_esymmSub_self (j : Fin n) :
    eLin j (esymmSub R n ((j : ℕ) + 1)) = (DualNumber.eps : DualNumber R) := by
  rw [eLin, eExpand_esymmSub, aeval_X, if_pos rfl]

/-- `eCoeff` is `1` on the elementary symmetric polynomial it names. -/
theorem eCoeff_esymmSub_self (j : Fin n) : eCoeff j (esymmSub R n ((j : ℕ) + 1)) = 1 := by
  rw [eCoeff, eLin_esymmSub_self, DualNumber.eps, TrivSqZeroExt.snd_inr]

/-- The `fst` of `eLin` is the constant term of the `e`-expansion; on an elementary
symmetric polynomial of positive index it vanishes. -/
theorem eLin_esymmSub_fst (j k : Fin n) :
    (eLin j (esymmSub R n ((k : ℕ) + 1))).fst = 0 := by
  rw [eLin, eExpand_esymmSub, aeval_X]
  by_cases h : k = j
  · rw [if_pos h, DualNumber.eps, TrivSqZeroExt.fst_inr]
  · rw [if_neg h, TrivSqZeroExt.fst_zero]

/-- **`eCoeff` kills decomposables.**  A product of two symmetric polynomials whose
`e`-expansions have vanishing constant term has vanishing linear coefficient: in the dual
numbers both factors land in the square-zero ideal. -/
theorem eCoeff_mul_eq_zero (j : Fin n) (f g : symmetricSubalgebra (Fin n) R)
    (hf : (eLin j f).fst = 0) (hg : (eLin j g).fst = 0) : eCoeff j (f * g) = 0 := by
  have hmul : eLin j (f * g) = eLin j f * eLin j g := by
    rw [eLin, eLin, eLin, eExpand_mul, map_mul]
  rw [eCoeff, hmul, TrivSqZeroExt.snd_mul, hf, hg]
  simp

/-- The `fst` of `eLin` on a product is the product of the `fst`s, so a factor with
vanishing constant term makes the whole product vanish there. -/
theorem eLin_mul_fst (j : Fin n) (f g : symmetricSubalgebra (Fin n) R) :
    (eLin j (f * g)).fst = (eLin j f).fst * (eLin j g).fst := by
  have hmul : eLin j (f * g) = eLin j f * eLin j g := by
    rw [eLin, eLin, eLin, eExpand_mul, map_mul]
  rw [hmul, TrivSqZeroExt.fst_mul]

end EExpand

end ParityP

end GroupApproximation.CharClass
