import GroupApproximation.KOne.LeavittKOneScalarQuotient
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Why the answer is `k^×/(k^×)^{d-1}`: the determinant on the degree-zero part

`non_mf_groups_exist.tex`, `cor:leavitt-mf-quotient` (tex line 1249):

> `H/EL_d(R) ≅ K₁(R) ≅ k^×/(k^×)^{d-1}`

`Manuscript/OneSidedMFRadical/LeavittKOneFormula.lean` reduces the second
isomorphism to two propositions.  One of them, `ScalarKernel` --- that a scalar
killed by `κ` is a `(d-1)`-st power --- is the half that needs an *invariant*
of `K₁(L_k(1,d))`: nothing else can distinguish two scalar classes.  This
module builds that invariant on the part of the algebra where it is elementary,
and isolates exactly what is missing.

## The mechanism

`L_k(1,d)` is `ℤ`-graded with degree-zero part the locally matricial algebra

    `L₀ = ⋃ₙ M_{dⁿ}(k)`,

the union taken along `A ↦ A ⊗ 1_d`.  On each stage the determinant is a
homomorphism `GL_{dⁿ}(k) → k^×`, and it is *not* compatible with the inclusions:

    `det (A ⊗ 1_d) = (det A)^d`      (`det_kroneckerRight`).

It becomes compatible exactly after dividing by `(d-1)`-st powers, because in
`k^×/(k^×)^{d-1}` one has `x^d = x · x^{d-1} = x` (`mk_pow_succ_eq_mk`).  So
`detMod k (d-1)` is a well-defined invariant of the whole degree-zero part
(`detMod_kroneckerRight_succ`), it kills every matrix of determinant `1` and in
particular every elementary matrix (`detMod_eq_one_of_det_eq_one`), and it sends
the scalar `c` at a single slot to the class of `c`
(`detMod_diagonal_single`).

**That congruence is the whole reason the printed answer is
`k^×/(k^×)^{d-1}` and not `k^×`.**  The exponent `d - 1` is not an artefact of
the presentation; it is the discrepancy between `det` and the inclusion of one
matrix stage in the next.

## What is missing, exactly

Nothing here reaches `K₁(L_k(1,d))`, because a unit of `L_k(1,d)` need not lie
in `L₀`.  Extending `detMod` from `L₀` to `L` is the Bass--Heller--Swan step for
the corner skew Laurent presentation `L = L₀[t₊,t₋;φ]`, equivalently the
Ara--Brustenga--Cortiñas sequence

    `K_n(k) --(1-d)--> K_n(k) → K_n(L_k(E)) → K_{n-1}(k)`

at the `d`-petal rose.  Both need `K₀` and `K₁` of a colimit of matrix algebras
together with a fundamental theorem, neither of which is on the tree.  So
`ScalarKernel` stays open, and this module is deliberately *not* a proof of it:
it is the invariant on the part of the ring where it exists, with the printed
exponent already visible.

## Nothing here is about the Leavitt algebra

Every statement below is about matrices over a field.  The `d` that appears is
the arity only through `Fin d` in the Kronecker factor.
-/

namespace GroupApproximation
namespace LeavittScalarQuotient

open scoped Kronecker

/-! ### The congruence `x^{m+1} ≡ x` modulo `m`-th powers -/

/-- **`x^{m+1} = x` in `G/Gᵐ`.**  At `m = d - 1` this is the reason the printed
answer group is `k^×/(k^×)^{d-1}`: raising to the `d`-th power is the identity
on it. -/
theorem mk_pow_succ_eq_mk {G : Type*} [CommGroup G] (m : ℕ) (a : G) :
    (QuotientGroup.mk (a ^ (m + 1)) : G ⧸ (powMonoidHom m : G →* G).range)
      = QuotientGroup.mk a := by
  refine QuotientGroup.eq.mpr ?_
  have hval : (a ^ (m + 1))⁻¹ * a = (a ^ m)⁻¹ := by
    rw [pow_succ]
    group
  rw [hval]
  exact inv_mem ⟨a, by rw [powMonoidHom_apply]⟩

end LeavittScalarQuotient

/-! ### The determinant modulo `m`-th powers -/

namespace LeavittDegreeZeroDeterminant

open scoped Kronecker
open LeavittScalarQuotient

variable (k : Type*) [Field k]

/-- **The determinant read modulo `m`-th powers.**  A homomorphism
`GL_ι(k) → k^×/(k^×)^m`. -/
noncomputable def detMod (m : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (Matrix ι ι k)ˣ →* (kˣ ⧸ (powMonoidHom m : kˣ →* kˣ).range) :=
  (QuotientGroup.mk' _).comp Matrix.GeneralLinearGroup.det

theorem detMod_apply (m : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A : (Matrix ι ι k)ˣ) :
    detMod k m ι A = QuotientGroup.mk (Matrix.GeneralLinearGroup.det A) := rfl

/-- **A matrix of determinant `1` has trivial invariant.**  In particular every
elementary matrix does, so `detMod` factors through the unstable `K₁` of the
stage. -/
theorem detMod_eq_one_of_det_eq_one (m : ℕ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : (Matrix ι ι k)ˣ)
    (hA : (A : Matrix ι ι k).det = 1) : detMod k m ι A = 1 := by
  rw [detMod_apply]
  refine (QuotientGroup.eq_one_iff _).mpr ?_
  have hone : Matrix.GeneralLinearGroup.det A = 1 := Units.ext hA
  rw [hone]
  exact one_mem _

/-- **The invariant of a diagonal matrix is the class of the product of its
entries.**  With a single non-unit slot this is the class of that entry. -/
theorem detMod_diagonal (m : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → kˣ) (A : (Matrix ι ι k)ˣ)
    (hA : (A : Matrix ι ι k) = Matrix.diagonal fun i ↦ ((u i : k))) :
    detMod k m ι A = QuotientGroup.mk (∏ i : ι, u i) := by
  have hdet : Matrix.GeneralLinearGroup.det A = ∏ i : ι, u i := by
    apply Units.ext
    show (A : Matrix ι ι k).det = ((∏ i : ι, u i : kˣ) : k)
    rw [hA, Matrix.det_diagonal]
    exact (map_prod (Units.coeHom k) u Finset.univ).symm
  rw [detMod_apply, hdet]

/-! ### The stage inclusion `A ↦ A ⊗ 1` -/

section Kronecker

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **The locally matricial inclusion `M_p(k) → M_{p·q}(k)`, `A ↦ A ⊗ 1`**, on
invertible matrices. -/
def kroneckerRight (A : (Matrix ι ι k)ˣ) : (Matrix (ι × κ) (ι × κ) k)ˣ where
  val := (A : Matrix ι ι k) ⊗ₖ (1 : Matrix κ κ k)
  inv := ((A⁻¹ : (Matrix ι ι k)ˣ) : Matrix ι ι k) ⊗ₖ (1 : Matrix κ κ k)
  val_inv := by
    rw [← Matrix.mul_kronecker_mul, A.mul_inv, one_mul,
      Matrix.one_kronecker_one]
  inv_val := by
    rw [← Matrix.mul_kronecker_mul, A.inv_mul, one_mul,
      Matrix.one_kronecker_one]

@[simp] theorem kroneckerRight_val (A : (Matrix ι ι k)ˣ) :
    ((kroneckerRight (κ := κ) k A : (Matrix (ι × κ) (ι × κ) k)ˣ) :
      Matrix (ι × κ) (ι × κ) k) = (A : Matrix ι ι k) ⊗ₖ (1 : Matrix κ κ k) :=
  rfl

/-- **`det (A ⊗ 1) = (det A)^q`.**  The determinant is *not* compatible with the
locally matricial inclusion: it is raised to the size of the new factor. -/
theorem det_kroneckerRight (A : (Matrix ι ι k)ˣ) :
    Matrix.GeneralLinearGroup.det (kroneckerRight (κ := κ) k A)
      = Matrix.GeneralLinearGroup.det A ^ Fintype.card κ := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  show ((A : Matrix ι ι k) ⊗ₖ (1 : Matrix κ κ k)).det
      = ((A : Matrix ι ι k).det) ^ Fintype.card κ
  rw [Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one]

end Kronecker

/-- **The invariant *is* compatible with the locally matricial inclusion, once
`(d-1)`-st powers are divided out.**

`det (A ⊗ 1_d) = (det A)^d` and `x^d = x` in `k^×/(k^×)^{d-1}`, so `detMod k
(d-1)` is constant along the tower `M_{dⁿ}(k) → M_{d^{n+1}}(k)` and therefore
descends to the degree-zero part `L₀ = ⋃ₙ M_{dⁿ}(k)` of `L_k(1,d)`.

`d` is written `m + 1`, so `m` is the printed `d - 1`. -/
theorem detMod_kroneckerRight_succ (m : ℕ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : (Matrix ι ι k)ˣ) :
    detMod k m (ι × Fin (m + 1)) (kroneckerRight (κ := Fin (m + 1)) k A)
      = detMod k m ι A := by
  rw [detMod_apply, detMod_apply, det_kroneckerRight, Fintype.card_fin]
  exact mk_pow_succ_eq_mk m (Matrix.GeneralLinearGroup.det A)

end LeavittDegreeZeroDeterminant
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.LeavittScalarQuotient.mk_pow_succ_eq_mk
#audit_axioms GroupApproximation.LeavittDegreeZeroDeterminant.detMod
#audit_axioms
  GroupApproximation.LeavittDegreeZeroDeterminant.detMod_eq_one_of_det_eq_one
#audit_axioms GroupApproximation.LeavittDegreeZeroDeterminant.detMod_diagonal
#audit_axioms GroupApproximation.LeavittDegreeZeroDeterminant.det_kroneckerRight
#audit_axioms
  GroupApproximation.LeavittDegreeZeroDeterminant.detMod_kroneckerRight_succ
