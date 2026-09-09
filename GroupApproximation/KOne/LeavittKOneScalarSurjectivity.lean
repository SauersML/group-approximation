import GroupApproximation.Leavitt.FamilyDescent
import GroupApproximation.Manuscript.OneSidedMFRadical.LeavittKOneFormula
import GroupApproximation.Meta.AxiomGuard

/-!
# `ScalarSurjective` from the printed Khanh--Thanh decomposition

`non_mf_groups_exist.tex`, proof of `cor:leavitt-mf-quotient` (tex line 1259):

> Khanh--Thanh show that `GL_d(R) = EL_d(R) D_d(k)`, where `D_d(k)` is the
> abelian group of diagonal matrices with entries in `k^×`

`Manuscript/OneSidedMFRadical/LeavittKOneFormula.lean` reduced the printed
identification `K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}` to two named propositions,
`ScalarSurjective` (every `K₁`-class is the class of a scalar) and
`ScalarKernel`.  This module closes the **first** of them from the printed
Khanh--Thanh sentence above and nothing else.

## Why this route and not the tree's own reduction

`LeavittKOneFormula.scalarSurjective_of_scalarReduction` derives the same
conclusion from `MatrixDiagonalization.ScalarReduction` **plus**
`CentralUnitsAreScalars`, i.e. `Z(L_k(1,d)) = k`.

The second of those is **no longer** the obstruction this docstring originally
recorded: `Leavitt/LeavittCenter.center_eq_bot` computes the centre and
`KOne/AryCentralUnitsAreScalars.lean` draws the consequence for units, so the
centre route is open and `ScalarReduction` is what remains of it.  The claim
that the centre was out of reach at every arity was true when this module was
written and is false now; it is corrected here rather than left standing.

The decomposition route is still worth having beside it, because it needs no
centre computation at all: the scalars are supplied by the decomposition
itself, since `D_d(k)` has entries in `k^×` by hypothesis.  It also needs no
countability of `k` and no perfectness of `EL_d(R)`, so the two routes have
genuinely different inputs.

`Manuscript/OneSidedMFRadical/KhanhThanhDiagonalDecomposition.PrintedKhanhThanhDecomposition`
is the same proposition as `PrintedKhanhThanhDiagonalDecomposition` below, and
that module's `printedKhanhThanhDecomposition_iff` and
`printedKhanhThanhDecomposition_of_diagAt` reduce it further; either name may be
fed to `scalarSurjective_of_khanhThanh`.

## The mechanism

Three facts already on the tree do the whole transport, through the ring
isomorphism `L_k(1,d) ≅ M_d(L_k(1,d))` packaged as
`CompleteMatrixFamily.unitsEquiv`:

* `CompleteMatrixFamily.unitsEquiv_elementaryGroup_mem_stableUnits` --- an
  elementary matrix pulls back to a **stably elementary** unit of the base
  ring, which `AlgebraicK.kappa_eq_one_of_mem_stableUnits` kills in `K₁`;
* `CompleteMatrixFamily.unitsEquiv_cornerDiagUnit` --- the diagonal matrix with
  a single unit slot pulls back to the corner insertion `pairKappaUnit`;
* `AlgebraicK.kappa_pairKappaUnit` --- corner insertion does not move a
  `κ`-class.

So a diagonal matrix, being a product of single-slot diagonals, has
`κ`-class the product of the `κ`-classes of its entries
(`exists_diagonalUnit_kappa`), and an elementary factor contributes nothing.
None of this is special to the Leavitt algebra: the general-ring section holds
for any ring with single-sandwich division carrying a complete matrix family.

## What remains open

`ScalarKernel` --- that a scalar killed by `κ` is a `(d-1)`-st power --- is
untouched here and is the only residue of `cor:leavitt-mf-quotient` after this
module and `LeavittMFQuotientKhanhThanhFree.lean`.  It needs an invariant of
`K₁(R)`, which nothing on the tree supplies.
-/

namespace GroupApproximation
namespace AlgebraicK

open MatrixDiagonalization CompleteMatrixFamily

/-! ### The general-ring transport -/

section General

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **An elementary matrix has trivial `κ` after descent.**  Through a complete
matrix family it pulls back into `stableUnits A`.  No division hypothesis and
no nontriviality: this direction is `FamilyDescent`'s inclusion composed with
`kappa_eq_one_of_mem_stableUnits`. -/
theorem kappa_unitsEquiv_elementary (F : CompleteMatrixFamily A ι)
    {E : (Matrix ι ι A)ˣ} (hE : E ∈ elementaryGroup ι A) :
    kappa A (F.unitsEquiv E) = 1 :=
  kappa_eq_one_of_mem_stableUnits (F.unitsEquiv_elementaryGroup_mem_stableUnits hE)

section Divisible

variable [Nontrivial A]

/-- **A single-slot diagonal keeps the `κ`-class of its entry.** -/
theorem kappa_unitsEquiv_cornerDiagUnit
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (F : CompleteMatrixFamily A ι) (i₀ : ι) (u : Aˣ) :
    kappa A (F.unitsEquiv (cornerDiagUnit i₀ u)) = kappa A u := by
  rw [F.unitsEquiv_cornerDiagUnit]
  exact kappa_pairKappaUnit hdiv _ _ _ u

/-- **Partial diagonals.**  For every finite set of slots there is a diagonal
unit carrying the prescribed entries there and `1` elsewhere, and its
`κ`-class after descent is the product of the `κ`-classes of the entries.

Stated with an existential rather than a product of `cornerDiagUnit`s because
`Aˣ` and `GL_ι(A)` are not commutative, so `Finset.prod` is unavailable on the
matrix side; the target `K₁(A)` is commutative, so the right-hand product is
an ordinary `Finset.prod`. -/
theorem exists_diagonalUnit_kappa
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (F : CompleteMatrixFamily A ι) (u : ι → Aˣ) :
    ∀ S : Finset ι, ∃ D : (Matrix ι ι A)ˣ,
      (D : Matrix ι ι A) =
          Matrix.diagonal (fun i ↦ if i ∈ S then ((u i : A)) else 1) ∧
        kappa A (F.unitsEquiv D) = ∏ i ∈ S, kappa A (u i) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_, ?_⟩
      · rw [Units.val_one, ← Matrix.diagonal_one]
        congr 1
      · rw [map_one, map_one, Finset.prod_empty]
  | insert a S haS IH =>
      obtain ⟨D, hDval, hDkappa⟩ := IH
      refine ⟨cornerDiagUnit a (u a) * D, ?_, ?_⟩
      · have hcorner : ((cornerDiagUnit a (u a) : (Matrix ι ι A)ˣ) :
            Matrix ι ι A) =
            Matrix.diagonal (fun j ↦ if j = a then ((u a : A)) else 1) := rfl
        rw [Units.val_mul, hcorner, hDval, Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        by_cases hja : j = a
        · subst hja
          simp [haS]
        · simp [hja]
      · rw [map_mul, map_mul, kappa_unitsEquiv_cornerDiagUnit hdiv F a (u a),
          hDkappa, Finset.prod_insert haS]

/-- **The full diagonal.**  The `κ`-class of a diagonal matrix, after descent
through the family, is the product of the `κ`-classes of its entries. -/
theorem exists_diagonalUnit_kappa_univ
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (F : CompleteMatrixFamily A ι) (u : ι → Aˣ) :
    ∃ D : (Matrix ι ι A)ˣ,
      (D : Matrix ι ι A) = Matrix.diagonal (fun i ↦ ((u i : A))) ∧
        kappa A (F.unitsEquiv D) = ∏ i : ι, kappa A (u i) := by
  obtain ⟨D, hDval, hDkappa⟩ :=
    exists_diagonalUnit_kappa hdiv F u (Finset.univ : Finset ι)
  refine ⟨D, ?_, hDkappa⟩
  rw [hDval]
  congr 1
  funext i
  rw [if_pos (Finset.mem_univ i)]

/-- **The transport, for a general ring.**  If an invertible matrix factors as
an elementary matrix times a diagonal one, then the unit of the base ring it
names has `κ`-class the product of the `κ`-classes of the diagonal entries. -/
theorem kappa_unitsEquiv_of_elementary_mul_diagonal
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (F : CompleteMatrixFamily A ι) (M E : (Matrix ι ι A)ˣ)
    (hE : E ∈ elementaryGroup ι A) (u : ι → Aˣ)
    (hM : (M : Matrix ι ι A) =
      (E : Matrix ι ι A) * Matrix.diagonal (fun i ↦ ((u i : A)))) :
    kappa A (F.unitsEquiv M) = ∏ i : ι, kappa A (u i) := by
  obtain ⟨D, hDval, hDkappa⟩ := exists_diagonalUnit_kappa_univ hdiv F u
  have hMED : M = E * D := by
    apply Units.ext
    rw [Units.val_mul, hDval, hM]
  rw [hMED, map_mul, map_mul, kappa_unitsEquiv_elementary F hE, one_mul, hDkappa]

end Divisible

end General

end AlgebraicK

/-! ### The Leavitt specialisation -/

namespace LeavittKOneScalar

open AryLeavitt AlgebraicK
open Manuscript.OneSidedMFRadical.LeavittKOneFormula

variable (k : Type) [Field k] (d : ℕ)

/-- **Khanh--Thanh's printed decomposition, as a named input.**

> `GL_d(R) = EL_d(R) D_d(k)`, where `D_d(k)` is the abelian group of diagonal
> matrices with entries in `k^×`

read as: every invertible `d × d` matrix over `L_k(1,d)` is an elementary
matrix times a diagonal matrix whose entries are scalars from `k^×`.  This is
the printed sentence at tex line 1259, in the form the `K₁` identification
consumes. -/
def PrintedKhanhThanhDiagonalDecomposition : Prop :=
  ∀ M : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ,
    ∃ E ∈ elementaryGroup (Fin d) (AryLeavittAlgebra k d), ∃ c : Fin d → kˣ,
      (M : Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d)) =
        (E : Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d)) *
          Matrix.diagonal
            (fun i ↦ algebraMap k (AryLeavittAlgebra k d) ((c i : k)))

/-- **`ScalarSurjective` from the printed Khanh--Thanh decomposition.**

Every class of `K₁(L_k(1,d))` is `κ` of a unit, that unit is a `d × d` matrix
over the algebra through the family identification, the decomposition splits it
into an elementary factor (which dies in `K₁`) and a scalar diagonal, and the
scalar diagonal contributes `α` of the product of its entries. -/
theorem scalarSurjective_of_khanhThanh (hd : 2 ≤ d)
    (hkt : PrintedKhanhThanhDiagonalDecomposition k d) :
    ScalarSurjective k d := by
  haveI : NeZero d := ⟨by omega⟩
  intro z
  obtain ⟨u, hu⟩ := kappa_surjective_aryLeavitt k d hd z
  obtain ⟨E, hE, c, hval⟩ := hkt ((AryLeavitt.family k d).unitsEquiv.symm u)
  -- `(scalarUnits k d c : R)` *is* `algebraMap k R c`, so `hval` already has
  -- the shape the transport lemma wants; only `rfl`-transparency separates
  -- them, which `rw` does not see.
  have hMval : (((AryLeavitt.family k d).unitsEquiv.symm u :
      (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) :
      Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d)) =
      (E : Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d)) *
        Matrix.diagonal (fun i ↦ ((scalarUnits k d (c i) :
          (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d)) := hval
  have hkappa := kappa_unitsEquiv_of_elementary_mul_diagonal
    (AryLeavitt.hasSingleSandwichDivision k d hd) (AryLeavitt.family k d)
    ((AryLeavitt.family k d).unitsEquiv.symm u) E hE
    (fun i ↦ scalarUnits k d (c i)) hMval
  rw [MulEquiv.apply_symm_apply] at hkappa
  refine ⟨∏ i : Fin d, c i, ?_⟩
  rw [← hu, hkappa, map_prod]
  exact Finset.prod_congr rfl fun i _ ↦ (alpha_apply k d (c i)).symm

/-- **The printed identification from Khanh--Thanh's decomposition and
`ScalarKernel`.**  `printedLeavittKOneFormula_of_inputs` with its first input
discharged. -/
theorem printedLeavittKOneFormula_of_khanhThanh (hd : 2 ≤ d)
    (hkt : PrintedKhanhThanhDiagonalDecomposition k d)
    (hker : ScalarKernel k d) :
    PrintedLeavittKOneFormula k d :=
  printedLeavittKOneFormula_of_inputs k d hd
    (scalarSurjective_of_khanhThanh k d hd hkt) hker

end LeavittKOneScalar
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AlgebraicK.kappa_unitsEquiv_elementary
#audit_axioms GroupApproximation.AlgebraicK.kappa_unitsEquiv_cornerDiagUnit
#audit_axioms GroupApproximation.AlgebraicK.exists_diagonalUnit_kappa_univ
#audit_axioms
  GroupApproximation.AlgebraicK.kappa_unitsEquiv_of_elementary_mul_diagonal
#audit_axioms GroupApproximation.LeavittKOneScalar.scalarSurjective_of_khanhThanh
#audit_axioms
  GroupApproximation.LeavittKOneScalar.printedLeavittKOneFormula_of_khanhThanh
