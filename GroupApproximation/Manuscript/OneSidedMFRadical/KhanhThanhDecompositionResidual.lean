import GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonalDecomposition
import GroupApproximation.KOne.LeavittKOneUnstableComparison
import GroupApproximation.KOne.AryCentralUnitsAreScalars
import GroupApproximation.Leavitt.AryWindowReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# `GL_d(R) = EL_d(R) D_d(k)`: the printed decomposition, reduced to one leaf

`non_mf_groups_exist.tex`, proof of `cor:leavitt-mf-quotient` (tex lines 1311--1317):

> Khanh--Thanh show that `GL_d(R) = EL_d(R)D_d(k)`, where `D_d(k)` is the abelian
> group of diagonal matrices with entries in `k^×`, which normalizes `EL_d(R)`, and
> that `K_1(R) ≅ k^×/(k^×)^{d-1}`.  So `[H,H] ≤ EL_d(R)`, while `EL_d(R) ≤ [H,H]` ...

`KhanhThanhDiagonalDecomposition.lean` proves three of the four claims of the first
sentence outright and reduces the fourth, the decomposition itself, to a statement
about single units (`printedKhanhThanhDecomposition_of_diagAt`).  This module closes
that reduction down to the rose-graph input, with no citation:

* `printedKhanhThanhDecomposition_of_scalarSurjective`: every `K₁`-class of
  `R = L_k(1,d)` being a scalar class (`LeavittKOneFormula.ScalarSurjective`) already
  gives the unstable, rank-`d` decomposition.  If `κ u = α a`, then `u a⁻¹` has trivial
  `κ`-class, so it is a stably elementary unit (`KOneDescent.aryLeavitt_kappa_ker`, no
  countability), and padding puts `diag(u a⁻¹, 1, …, 1)` in `EL_d(R)`
  (`KOneDescent.diagAt_mem_elementaryGroup_of_mem_stableUnits`).
* `printedKhanhThanhDecomposition_of_narrowReduction`: `ScalarSurjective` follows from
  `AryLeavitt.NarrowReduction k d` through `scalarReduction_of_narrowReduction` and the
  centre computation (`AryLeavitt.scalarSurjective_of_scalarReduction_ary`).

So the printed decomposition, at every field `k` and every `d ≥ 2`, rests on exactly
one proposition, `AryLeavitt.NarrowReduction k d`: every unit of `L_k(1,d)` whose value
lies in the degree window `[-1, 1]` is a central scalar modulo the stably elementary
units.  At `d = 2` that is `KOne/RefineLoopDischarge.lean`; at arity `d` it is the pencil
development being ported.

The printed consequence "So `[H,H] ≤ EL_d(R)`" is carried along the printed route by
`commutator_le_elementaryGroup_of_printedDecomposition`: from the decomposition, with
`D_d(k)` abelian and `EL_d(R)` normal, the quotient `GL_d(R)/EL_d(R)` is abelian.  (The
same inclusion is already proved unconditionally by a different route, Gaussian
elimination plus Whitehead's identity, in `LeavittMFQuotientKhanhThanhFree.lean`.)
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace KhanhThanhDiagonal

open AryLeavitt RankNElimination MatrixDiagonalization
open scoped commutatorElement

variable (k : Type) [Field k] (d : ℕ)

/-- `diagAt` at the first index is multiplicative: the quotient of two first-slot
diagonal units is the first-slot diagonal of the quotient. -/
theorem diagAt_firstIndex_mul_inv (hd : 2 ≤ d) (u v : (AryLeavittAlgebra k d)ˣ) :
    (diagAt (firstIndex d hd) u :
        (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) *
      (diagAt (firstIndex d hd) v)⁻¹ =
      diagAt (⟨0, by omega⟩ : Fin d) (u * v⁻¹) := by
  calc (diagAt (firstIndex d hd) u :
          (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) *
        (diagAt (firstIndex d hd) v)⁻¹
      = diagAtHom (firstIndex d hd) u * (diagAtHom (firstIndex d hd) v)⁻¹ := rfl
    _ = diagAtHom (firstIndex d hd) (u * v⁻¹) := by rw [map_mul, map_inv]
    _ = diagAt (⟨0, by omega⟩ : Fin d) (u * v⁻¹) := rfl

/-- **The printed decomposition from `K₁`-surjectivity of the scalars.**

If every class of `K₁(L_k(1,d))` is the class of a scalar, then every invertible
`d × d` matrix over `L_k(1,d)` is an elementary matrix times a diagonal matrix with
entries in `k^×`.  The proof is unstable: a unit `u` with `κ u = α a` has `u a⁻¹`
stably elementary, and the first-slot diagonal of a stably elementary unit is already
elementary at rank `d`. -/
theorem printedKhanhThanhDecomposition_of_scalarSurjective (hd : 2 ≤ d)
    (hs : LeavittKOneFormula.ScalarSurjective k d) :
    PrintedKhanhThanhDecomposition k d := by
  refine printedKhanhThanhDecomposition_of_diagAt k d hd ?_
  intro u
  obtain ⟨a, ha⟩ := hs (AlgebraicK.kappa (AryLeavittAlgebra k d) u)
  refine ⟨a, ?_⟩
  have hw : u * (LeavittKOneFormula.scalarUnits k d a)⁻¹ ∈
      stableUnits (AryLeavittAlgebra k d) := by
    rw [← KOneDescent.aryLeavitt_kappa_ker k d hd, MonoidHom.mem_ker, map_mul,
      map_inv, ← LeavittKOneFormula.alpha_apply k d a, ha, mul_inv_cancel]
  rw [diagAt_firstIndex_mul_inv k d hd]
  exact KOneDescent.diagAt_mem_elementaryGroup_of_mem_stableUnits hd (by omega) hw

/-- **The printed decomposition from the narrow-window kill**, at every field and every
`d ≥ 2`.  `NarrowReduction k d` is the single remaining input. -/
theorem printedKhanhThanhDecomposition_of_narrowReduction (hd : 2 ≤ d)
    (hn : AryLeavitt.NarrowReduction k d) : PrintedKhanhThanhDecomposition k d :=
  printedKhanhThanhDecomposition_of_scalarSurjective k d hd
    (AryLeavitt.scalarSurjective_of_scalarReduction_ary k d hd
      (AryLeavitt.scalarReduction_of_narrowReduction k d hd hn))

/-- The same conclusion in the spelling `KOne/LeavittKOneScalarSurjectivity.lean`
consumes; the two propositions have the same body. -/
theorem printedKhanhThanhDiagonalDecomposition_of_narrowReduction (hd : 2 ≤ d)
    (hn : AryLeavitt.NarrowReduction k d) :
    LeavittKOneScalar.PrintedKhanhThanhDiagonalDecomposition k d :=
  printedKhanhThanhDecomposition_of_narrowReduction k d hd hn

/-- **"So `[H,H] ≤ EL_d(R)`"**, along the printed route.

> Khanh--Thanh show that `GL_d(R)=EL_d(R)D_d(k)`, where `D_d(k)` is the abelian group of
> diagonal matrices with entries in `k^×`, which normalizes `EL_d(R)` ... So
> `[H,H] ≤ EL_d(R)`

Every invertible matrix is congruent modulo the normal subgroup `EL_d(R)` to an element
of `D_d(k)`, and `D_d(k)` is abelian, so the quotient `GL_d(R)/EL_d(R)` is abelian and
contains no nontrivial commutator. -/
theorem commutator_le_elementaryGroup_of_printedDecomposition (hd : 2 ≤ d)
    (hkt : PrintedKhanhThanhDecomposition k d) :
    commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ≤
      elementaryGroup (Fin d) (AryLeavittAlgebra k d) := by
  haveI : (elementaryGroup (Fin d) (AryLeavittAlgebra k d)).Normal :=
    elementaryGroup_normal_ary k d hd
  have hq : ∀ X ∈ elementaryGroup (Fin d) (AryLeavittAlgebra k d),
      (QuotientGroup.mk' (elementaryGroup (Fin d) (AryLeavittAlgebra k d))) X = 1 :=
    fun X hX ↦ (QuotientGroup.eq_one_iff X).mpr hX
  have hsplit : ∀ M : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ,
      ∃ C ∈ printedDiagonal k d,
        (QuotientGroup.mk' (elementaryGroup (Fin d) (AryLeavittAlgebra k d))) M =
          (QuotientGroup.mk' (elementaryGroup (Fin d) (AryLeavittAlgebra k d))) C := by
    intro M
    obtain ⟨E, hE, c, hval⟩ := hkt M
    obtain ⟨C, hCmem, hCval⟩ := exists_mem_printedDiagonal k d c
    have hMEC : M = E * C := Units.ext (by rw [Units.val_mul, hCval, hval])
    exact ⟨C, hCmem, by rw [hMEC, map_mul, hq E hE, one_mul]⟩
  rw [commutator_def, Subgroup.commutator_le]
  intro A _ B _
  obtain ⟨C₁, hC₁, h₁⟩ := hsplit A
  obtain ⟨C₂, hC₂, h₂⟩ := hsplit B
  have hzero : (QuotientGroup.mk' (elementaryGroup (Fin d) (AryLeavittAlgebra k d)))
      ⁅A, B⁆ = 1 := by
    rw [map_commutatorElement, h₁, h₂, ← map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr (printedDiagonal_mul_comm k d hC₁ hC₂),
      map_one]
  have hker : ⁅A, B⁆ ∈
      (QuotientGroup.mk' (elementaryGroup (Fin d) (AryLeavittAlgebra k d))).ker :=
    MonoidHom.mem_ker.mpr hzero
  rwa [QuotientGroup.ker_mk'] at hker

end KhanhThanhDiagonal
end OneSidedMFRadical
end Manuscript
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.diagAt_firstIndex_mul_inv
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.printedKhanhThanhDecomposition_of_scalarSurjective
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.printedKhanhThanhDecomposition_of_narrowReduction
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.printedKhanhThanhDiagonalDecomposition_of_narrowReduction
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.commutator_le_elementaryGroup_of_printedDecomposition
