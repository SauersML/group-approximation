import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# The carry substitution of the char-`p` parameter-coordinate host (lane bh-met-01)

Research node `positive-char-polynomial-affine-groups-are-self-similar-proof`, step 4
("Substitution" and "Divisibility").  For `R = F_p[s_0, ..., s_{k-1}]` (the node writes
`s_1, ..., s_k`, with `s_1` the uniformizer) and a first-level parameter `α`, the substitution

  `σ_α : s_0 ↦ s_0,   s_i ↦ α_i + s_0 s_i   (i ≠ 0)`

is a unital ring endomorphism, and for every `P`

  `s_0 ∣ σ_α(P) - P(0, α)`,

so the state `(σ_α(g) e + σ_α(b) - c) / s_0` of the node is a polynomial.

Everything is proved over an arbitrary commutative ring `R` and index type `ι` with a
distinguished uniformizer index `i₀`; `charPSubst`/`charPCarry` specialize to
`MvPolynomial (Fin k) (ZMod p)` with `i₀ = 0`.  The parameter is `α : ι → R`, and `α i₀` is
not used.  (Primality of `p` is not needed for the carry lemma.)

**Route.** `exists_eq_C_eval_add_X_mul`: if an `R`-algebra endomorphism `φ` satisfies
`φ(X_i) ≡ β_i (mod X_{i₀})` for every `i`, then `φ(P) ≡ P(β) (mod X_{i₀})` for every `P`; this
is induction over `MvPolynomial.induction_on` (constants, sums, multiplication by a
variable).  For `σ_α` the hypothesis is immediate with
`β = carryBase i₀ α = (0 at i₀, α elsewhere)`.

Main declarations:
* `carrySubst i₀ α`, with `carrySubst_X_self`, `carrySubst_X_of_ne`;
* `carrySubst_exists`, `X_dvd_carrySubst_sub` (the carry lemma);
* `carryQuot`, `carrySubst_eq_add_carryQuot`, `carryQuot_unique` (the quotient by `s_0`);
* `charPSubst`, `charPCarry` (the specialization to `F_p[s_0, ..., s_{k-1}]`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharPHost

open MvPolynomial

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

/-- The images of the variables under the carry substitution: `X i₀ ↦ X i₀` and
`X i ↦ C (α i) + X i₀ * X i` for `i ≠ i₀`. -/
noncomputable def carryImage (i₀ : ι) (α : ι → R) (i : ι) : MvPolynomial ι R :=
  if i = i₀ then X i₀ else C (α i) + X i₀ * X i

/-- The carry substitution `σ_α` of the node, as an `R`-algebra endomorphism. -/
noncomputable def carrySubst (i₀ : ι) (α : ι → R) :
    MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
  aeval (carryImage i₀ α)

/-- The evaluation point `(0, α)`: the uniformizer coordinate is `0`, the others are `α`. -/
def carryBase (i₀ : ι) (α : ι → R) (i : ι) : R :=
  if i = i₀ then 0 else α i

theorem carrySubst_X_self (i₀ : ι) (α : ι → R) : carrySubst i₀ α (X i₀) = X i₀ := by
  rw [carrySubst, MvPolynomial.aeval_X, carryImage, if_pos rfl]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.carrySubst_X_self

theorem carrySubst_X_of_ne (i₀ : ι) (α : ι → R) {i : ι} (hi : i ≠ i₀) :
    carrySubst i₀ α (X i) = C (α i) + X i₀ * X i := by
  rw [carrySubst, MvPolynomial.aeval_X, carryImage, if_neg hi]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.carrySubst_X_of_ne

omit [DecidableEq ι] in
/-- **Carry criterion.** If an `R`-algebra endomorphism of `R[X_ι]` sends every variable `X_i` to
`β_i` modulo `X_{i₀}`, then it sends every polynomial `P` to `P(β)` modulo `X_{i₀}`. -/
theorem exists_eq_C_eval_add_X_mul (i₀ : ι) (φ : MvPolynomial ι R →ₐ[R] MvPolynomial ι R)
    (β : ι → R) (hφ : ∀ i, ∃ Q, φ (X i) = C (β i) + X i₀ * Q) (P : MvPolynomial ι R) :
    ∃ Q, φ P = C (eval β P) + X i₀ * Q := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_⟩
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, mul_zero,
      add_zero]
  | add p q hp hq =>
    obtain ⟨Q₁, hQ₁⟩ := hp
    obtain ⟨Q₂, hQ₂⟩ := hq
    refine ⟨Q₁ + Q₂, ?_⟩
    simp only [map_add, hQ₁, hQ₂]
    ring
  | mul_X p n hp =>
    obtain ⟨Q, hQ⟩ := hp
    obtain ⟨Q', hQ'⟩ := hφ n
    refine ⟨C (eval β p) * Q' + Q * φ (X n), ?_⟩
    simp only [map_mul, MvPolynomial.eval_X, hQ, hQ']
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.exists_eq_C_eval_add_X_mul

/-- The variables satisfy the carry criterion for `σ_α` at the point `(0, α)`. -/
theorem carrySubst_X_exists (i₀ : ι) (α : ι → R) (i : ι) :
    ∃ Q, carrySubst i₀ α (X i) = C (carryBase i₀ α i) + X i₀ * Q := by
  by_cases hi : i = i₀
  · subst hi
    refine ⟨1, ?_⟩
    rw [carrySubst_X_self, carryBase, if_pos rfl, map_zero, zero_add, mul_one]
  · refine ⟨X i, ?_⟩
    rw [carrySubst_X_of_ne i₀ α hi, carryBase, if_neg hi]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.carrySubst_X_exists

/-- **The carry lemma**, existence form: `σ_α(P) = P(0, α) + s_0 · Q` for some polynomial
`Q`. -/
theorem carrySubst_exists (i₀ : ι) (α : ι → R) (P : MvPolynomial ι R) :
    ∃ Q, carrySubst i₀ α P = C (eval (carryBase i₀ α) P) + X i₀ * Q :=
  exists_eq_C_eval_add_X_mul i₀ (carrySubst i₀ α) (carryBase i₀ α)
    (carrySubst_X_exists i₀ α) P

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.carrySubst_exists

/-- **The carry lemma**: `s_0 ∣ σ_α(P) - P(0, α)`. -/
theorem X_dvd_carrySubst_sub (i₀ : ι) (α : ι → R) (P : MvPolynomial ι R) :
    X i₀ ∣ carrySubst i₀ α P - C (eval (carryBase i₀ α) P) := by
  obtain ⟨Q, hQ⟩ := carrySubst_exists i₀ α P
  exact Dvd.intro Q (by rw [hQ, add_sub_cancel_left])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.X_dvd_carrySubst_sub

/-- The carry quotient `(σ_α(P) - P(0, α)) / s_0`. -/
noncomputable def carryQuot (i₀ : ι) (α : ι → R) (P : MvPolynomial ι R) :
    MvPolynomial ι R :=
  Classical.choose (carrySubst_exists i₀ α P)

theorem carrySubst_eq_add_carryQuot (i₀ : ι) (α : ι → R) (P : MvPolynomial ι R) :
    carrySubst i₀ α P = C (eval (carryBase i₀ α) P) + X i₀ * carryQuot i₀ α P :=
  Classical.choose_spec (carrySubst_exists i₀ α P)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.carrySubst_eq_add_carryQuot

/-- Over a domain the carry quotient is unique. -/
theorem carryQuot_unique [IsDomain R] (i₀ : ι) (α : ι → R) (P Q : MvPolynomial ι R)
    (hQ : carrySubst i₀ α P = C (eval (carryBase i₀ α) P) + X i₀ * Q) :
    Q = carryQuot i₀ α P :=
  mul_left_cancel₀ (MvPolynomial.X_ne_zero (R := R) i₀) (add_left_cancel (hQ.symm.trans
    (carrySubst_eq_add_carryQuot i₀ α P)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.carryQuot_unique

/-! ### The specialization to `F_p[s_0, ..., s_{k-1}]` -/

/-- `σ_α` on `MvPolynomial (Fin k) (ZMod p)`: `s_0 ↦ s_0` and `s_i ↦ α_i + s_0 s_i` for
`i ≠ 0` (the value `α 0` is not used). -/
noncomputable def charPSubst (p k : ℕ) [NeZero k] (α : Fin k → ZMod p) :
    MvPolynomial (Fin k) (ZMod p) →ₐ[ZMod p] MvPolynomial (Fin k) (ZMod p) :=
  carrySubst (0 : Fin k) α

theorem charPSubst_X_zero (p k : ℕ) [NeZero k] (α : Fin k → ZMod p) :
    charPSubst p k α (X (0 : Fin k)) = X 0 :=
  carrySubst_X_self (0 : Fin k) α

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.charPSubst_X_zero

theorem charPSubst_X_of_ne (p k : ℕ) [NeZero k] (α : Fin k → ZMod p) {i : Fin k}
    (hi : i ≠ 0) :
    charPSubst p k α (X i) = C (α i) + X 0 * X i :=
  carrySubst_X_of_ne (0 : Fin k) α hi

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.charPSubst_X_of_ne

/-- **Char-`p` carry lemma** (lane bh-met-01): `s_0 ∣ σ_α(P) - P(0, α)` in
`F_p[s_0, ..., s_{k-1}]`, where `P(0, α)` is evaluation at the point with coordinate `0` at `s_0`
and `α_i` at `s_i`. -/
theorem charPCarry (p k : ℕ) [NeZero k] (α : Fin k → ZMod p)
    (P : MvPolynomial (Fin k) (ZMod p)) :
    X (0 : Fin k) ∣ charPSubst p k α P - C (eval (carryBase (0 : Fin k) α) P) :=
  X_dvd_carrySubst_sub (0 : Fin k) α P

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.charPCarry

end CharPHost
end Metabelian
end BooneHigman
end GroupApproximation
