import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Data.Fintype.Option
import GroupApproximation.Meta.AxiomGuard

/-!
# Invariant spaces of weighted polynomial functions (bh-met-87c, part 3)

Let `N` be an abelian group with coordinates `co : N → σ → L`, where `σ` is finite and
`co` is injective, and fix weights `w : σ → ℕ`, all positive.

* `eHighWitt_polySpace w co d` is the space of functions `N → L` of the form
  `x ↦ Φ(co x)`, where `Φ` has weighted degree `≤ d`.
* Degree `≤ d` is encoded by homogenizing.  We take variables `Option σ`, where `none` is an
  extra variable `t` of weight `1` that is evaluated at `1`, and ask `Φ` to be weighted
  homogeneous of degree exactly `d`.  This keeps Mathlib's API usable
  (`weightedHomogeneousSubmodule_fg`, `.mul`, `.pow`, `.prod`, `.sum`).
* `eHighWitt_IsWeightPoly w co g` says that `g : N → N` is a weight-polynomial map: each
  coordinate `co (g x) v` is `Φᵥ(co x)` for a homogenized `Φᵥ` of weighted degree `w v`.

Main result: `eHighWitt_exists_polyFun_of_weightPoly`.  Suppose translations and a family
`act q` are weight-polynomial, and `w v ≤ d` for all `v`.  Then the space is:

* finite-dimensional;
* stable under translation and under `act`;
* separating.

The proof is substitution (`bind₁`), which preserves weighted homogeneity when every
substituted polynomial has the weight of its variable.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

open MvPolynomial

noncomputable section

variable {L : Type} [Field L] {σ : Type}

/-- Homogenized weights: the extra variable `none` has weight `1`. -/
def eHighWitt_hwt (w : σ → ℕ) : Option σ → ℕ := fun o => Option.elim o 1 w

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_hwt

/-- The homogenized point: the extra variable `none` is evaluated at `1`. -/
def eHighWitt_hpt (c : σ → L) : Option σ → L := fun o => Option.elim o 1 c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_hpt

/-- `g` is weight-polynomial: each coordinate `co (g x) v` is a homogenized polynomial of
weighted degree `w v` in the coordinates of `x`. -/
def eHighWitt_IsWeightPoly {N : Type} (w : σ → ℕ) (co : N → σ → L) (g : N → N) : Prop :=
  ∀ v : σ, ∃ Φ : MvPolynomial (Option σ) L,
    IsWeightedHomogeneous (eHighWitt_hwt w) Φ (w v) ∧
      ∀ x : N, co (g x) v = aeval (eHighWitt_hpt (co x)) Φ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_IsWeightPoly

/-- Evaluation of homogenized polynomials at the coordinates of points of `N`. -/
def eHighWitt_evalMap {N : Type} (co : N → σ → L) :
    MvPolynomial (Option σ) L →ₗ[L] (N → L) :=
  LinearMap.pi fun x => (aeval (eHighWitt_hpt (co x))).toLinearMap

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_evalMap

theorem eHighWitt_evalMap_apply {N : Type} (co : N → σ → L) (P : MvPolynomial (Option σ) L)
    (x : N) : eHighWitt_evalMap co P x = aeval (eHighWitt_hpt (co x)) P := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_evalMap_apply

/-- Functions on `N` given by polynomials of weighted degree `≤ d` in the coordinates. -/
def eHighWitt_polySpace {N : Type} (w : σ → ℕ) (co : N → σ → L) (d : ℕ) :
    Submodule L (N → L) :=
  (weightedHomogeneousSubmodule L (eHighWitt_hwt w) d).map (eHighWitt_evalMap co)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_polySpace

theorem eHighWitt_isWH_of_eq {τ : Type} {w : τ → ℕ} {φ : MvPolynomial τ L} {m n : ℕ}
    (h : IsWeightedHomogeneous w φ m) (hmn : m = n) : IsWeightedHomogeneous w φ n :=
  hmn ▸ h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_isWH_of_eq

theorem eHighWitt_isWH_X_pow (w : σ → ℕ) (o : Option σ) (k : ℕ) :
    IsWeightedHomogeneous (eHighWitt_hwt w) (X o ^ k : MvPolynomial (Option σ) L)
      (eHighWitt_hwt w o * k) := by
  induction k with
  | zero =>
    rw [pow_zero, mul_zero]
    exact isWeightedHomogeneous_one L _
  | succ k ih =>
    rw [pow_succ, mul_add_one]
    exact ih.mul (isWeightedHomogeneous_X L _ o)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_isWH_X_pow

/-- Substituting polynomials of the right weights preserves weighted homogeneity. -/
theorem eHighWitt_isWH_bind₁ {τ υ : Type} {w : τ → ℕ} {w' : υ → ℕ}
    (ψ : τ → MvPolynomial υ L) (hψ : ∀ i, IsWeightedHomogeneous w' (ψ i) (w i))
    {P : MvPolynomial τ L} {d : ℕ} (hP : IsWeightedHomogeneous w P d) :
    IsWeightedHomogeneous w' (bind₁ ψ P) d := by
  rw [P.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  show IsWeightedHomogeneous w' (bind₁ ψ (monomial m (coeff m P))) d
  have hmd := (Finsupp.weight_apply w m).symm.trans (hP (mem_support_iff.mp hm))
  rw [bind₁_monomial, ← hmd]
  exact (IsWeightedHomogeneous.prod m.support (fun i => ψ i ^ m i) (fun i => m i • w i)
    fun i _ => (hψ i).pow (m i)).C_mul _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_isWH_bind₁

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
