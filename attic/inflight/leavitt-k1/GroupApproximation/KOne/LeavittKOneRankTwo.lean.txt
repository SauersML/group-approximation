import GroupApproximation.Leavitt.LeavittSelfSimilarity
import GroupApproximation.KOne.ClassicalKOne
import GroupApproximation.KOne.AlgebraicKOneFunctor
import GroupApproximation.KOne.LeavittKOneScalarQuotient
import GroupApproximation.Manuscript.OneSidedMFRadical.LeavittKOneFormula
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:leavitt-mf-quotient`'s `K₁` identification, closed at `d = 2`

`non_mf_groups_exist.tex`, `cor:leavitt-mf-quotient` (tex line 1302) and the
sentence after it (tex line 1320):

> `H/EL_d(R) ≅ K₁(R) ≅ k^×/(k^×)^{d-1}`

> For `d=2` the quotient is trivial for every countable field `k`.

`Manuscript/OneSidedMFRadical/LeavittKOneFormula.lean` reduces the second
isomorphism to two propositions, `ScalarSurjective` and `ScalarKernel`, both
stated for the `d`-ary universal algebra `AryLeavittAlgebra k d`.  This module
closes **both**, and hence `PrintedLeavittKOneFormula`, at `d = 2`.

## Why this needed a module and not a one-liner

The tree's `K₁(L_k(1,2)) = 0` (`binaryLeavittClassicalK1_subsingleton`) is about
`BinaryLeavitt.BinaryLeavittAlgebra k`, the four-generator presentation, while
every general-`d` statement of the manuscript development is about
`AryLeavitt.AryLeavittAlgebra k d`, the `2d`-generator one.  The two are the
same algebra, but nothing on the tree said so.  `aryBinaryAlgEquiv` supplies the
missing isomorphism, from the two universal properties (`AryLeavitt.lift` and
`BinaryLeavitt.lift`) and a generator check on each side.

With it, `K₁` transports along `AlgebraicK.algebraicKOneCongr`, and the two
propositions collapse: `K₁` is trivial, so every class is a scalar class, and
`k^×/(k^×)^{2-1}` is the whole group, so the kernel condition is vacuous.

## Calibration: this case proves nothing about `d ≥ 3`

Both propositions hold here for the *degenerate* reason and neither is tested:
`ScalarSurjective` says a trivial group is covered, and `ScalarKernel` reads
`c = e^1`, true with `e = c` because `(k^×)^{2-1} = k^×`
(`LeavittScalarQuotient.range_powMonoidHom_one`).  The first informative case is
`d = 3` over a field with a non-square unit.  Nothing here should be read as
evidence about the general identification, which is proved at every `d ≥ 2` by
other arguments: `KhanhThanhDiagonal.scalarSurjective_holds` and
`LeavittKOneFormula.scalarKernel`.
-/

namespace GroupApproximation
namespace AryLeavittRankTwo

open AryLeavitt

variable (k : Type) [Field k]

/-! ### The `2`-ary universal algebra carries a binary Leavitt family -/

/-- The binary Leavitt family of the `2`-ary universal presentation. -/
def aryLeavittFamily : LeavittFamily (AryLeavittAlgebra k 2) where
  s0 := genS k 2 0
  s1 := genS k 2 1
  t0 := genT k 2 0
  t1 := genT k 2 1
  -- `simp` will not unfold `(family k 2).left` to `genS`; the two are
  -- definitionally equal, so the `if` is discharged by `rw` and the rest by
  -- `exact`.
  t0_s0 := by
    have h := (family k 2).orthogonal 0 0
    rw [if_pos rfl] at h
    exact h
  t0_s1 := by
    have h := (family k 2).orthogonal 0 1
    rw [if_neg (by decide : ¬((0 : Fin 2) = 1))] at h
    exact h
  t1_s0 := by
    have h := (family k 2).orthogonal 1 0
    rw [if_neg (by decide : ¬((1 : Fin 2) = 0))] at h
    exact h
  t1_s1 := by
    have h := (family k 2).orthogonal 1 1
    rw [if_pos rfl] at h
    exact h
  sum_range := by
    have h := (family k 2).complete
    rw [Fin.sum_univ_two] at h
    exact h

/-! ### The two universal maps -/

/-- `L_k(1,2)` in the `d`-ary presentation, mapped to the binary presentation by
its universal property. -/
noncomputable def toBinary :
    AryLeavittAlgebra k 2 →ₐ[k] BinaryLeavitt.BinaryLeavittAlgebra k :=
  AryLeavitt.lift (BinaryLeavitt.family k).binaryMatrixFamily

/-- The binary presentation, mapped to the `d`-ary one by its universal
property. -/
noncomputable def fromBinary :
    BinaryLeavitt.BinaryLeavittAlgebra k →ₐ[k] AryLeavittAlgebra k 2 :=
  BinaryLeavitt.lift (aryLeavittFamily k)

@[simp] theorem fromBinary_generator (g : BinaryLeavitt.Generator) :
    fromBinary k (BinaryLeavitt.generator k g) =
      ![genS k 2 0, genS k 2 1, genT k 2 0, genT k 2 1] g :=
  BinaryLeavitt.lift_generator (aryLeavittFamily k) g

@[simp] theorem toBinary_genS (i : Fin 2) :
    toBinary k (genS k 2 i) =
      ![BinaryLeavitt.generator k BinaryLeavitt.s0,
        BinaryLeavitt.generator k BinaryLeavitt.s1] i :=
  AryLeavitt.lift_genS _ i

@[simp] theorem toBinary_genT (i : Fin 2) :
    toBinary k (genT k 2 i) =
      ![BinaryLeavitt.generator k BinaryLeavitt.t0,
        BinaryLeavitt.generator k BinaryLeavitt.t1] i :=
  AryLeavitt.lift_genT _ i

/-! ### The two maps are mutually inverse -/

-- The four generator cases of each round trip need different entries of the
-- `![…]` vectors and different generator names, so a single `simp` list covers
-- lemmas that no individual branch uses all of.
set_option linter.unusedSimpArgs false in
theorem toBinary_comp_fromBinary :
    (toBinary k).comp (fromBinary k) =
      AlgHom.id k (BinaryLeavitt.BinaryLeavittAlgebra k) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  show toBinary k (fromBinary k (BinaryLeavitt.generator k g)) =
    BinaryLeavitt.generator k g
  fin_cases g <;>
    simp [BinaryLeavitt.s0, BinaryLeavitt.s1, BinaryLeavitt.t0,
      BinaryLeavitt.t1]

set_option linter.unusedSimpArgs false in
theorem fromBinary_comp_toBinary :
    (fromBinary k).comp (toBinary k) = AlgHom.id k (AryLeavittAlgebra k 2) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  cases g with
  | inl i =>
      show fromBinary k (toBinary k (genS k 2 i)) = genS k 2 i
      fin_cases i <;>
        simp [BinaryLeavitt.s0, BinaryLeavitt.s1, BinaryLeavitt.t0,
          BinaryLeavitt.t1]
  | inr i =>
      show fromBinary k (toBinary k (genT k 2 i)) = genT k 2 i
      fin_cases i <;>
        simp [BinaryLeavitt.s0, BinaryLeavitt.s1, BinaryLeavitt.t0,
          BinaryLeavitt.t1]

/-- **The two universal presentations of `L_k(1,2)` agree.**  The `2`-ary
algebra of `AryLeavitt` and the four-generator algebra of `BinaryLeavitt` are
isomorphic as `k`-algebras. -/
noncomputable def aryBinaryAlgEquiv :
    AryLeavittAlgebra k 2 ≃ₐ[k] BinaryLeavitt.BinaryLeavittAlgebra k :=
  AlgEquiv.ofAlgHom (toBinary k) (fromBinary k) (toBinary_comp_fromBinary k)
    (fromBinary_comp_toBinary k)

/-! ### `K₁` at `d = 2` -/

/-- **`K₁(L_k(1,2)) = 0` in the `d`-ary vocabulary.**  Transported from
`binaryLeavittClassicalK1_subsingleton` along the presentation isomorphism. -/
theorem subsingleton_algebraicKOne :
    Subsingleton (AlgebraicK.AlgebraicKOne (AryLeavittAlgebra k 2)) := by
  haveI : Subsingleton
      (AlgebraicK.AlgebraicKOne (BinaryLeavitt.BinaryLeavittAlgebra k)) :=
    binaryLeavittClassicalK1_subsingleton k
  exact (AlgebraicK.algebraicKOneCongr
    (aryBinaryAlgEquiv k).toRingEquiv).injective.subsingleton

end AryLeavittRankTwo

/-! ### The two propositions, at `d = 2` -/

namespace LeavittKOneRankTwo

open Manuscript.OneSidedMFRadical.LeavittKOneFormula
open AryLeavittRankTwo

variable (k : Type) [Field k]

/-- **`ScalarSurjective` at `d = 2`**, for the degenerate reason: the target is
trivial. -/
theorem scalarSurjective : ScalarSurjective k 2 := by
  haveI := subsingleton_algebraicKOne k
  show Function.Surjective (alpha k 2)
  intro _
  exact ⟨1, Subsingleton.elim _ _⟩

/-- **`ScalarKernel` at `d = 2`**, for the degenerate reason: `(k^×)^{2-1}` is
all of `k^×`. -/
theorem scalarKernel : ScalarKernel k 2 := by
  show (alpha k 2).ker ≤ unitPowSubgroup k (2 - 1)
  intro x _
  have htop : unitPowSubgroup k (2 - 1) = ⊤ :=
    LeavittScalarQuotient.range_powMonoidHom_one kˣ
  rw [htop]
  exact Subgroup.mem_top x

/-- **The printed identification `K₁(R) ≅ k^×/(k^×)^{d-1}`, closed at `d = 2`.**

The first genuinely closed instance of `PrintedLeavittKOneFormula`.  Both sides
are trivial groups, so the isomorphism carries no information about `d ≥ 3`;
what it does settle is that the printed statement is correct where the tree can
check it, in the same vocabulary the general-`d` development uses. -/
theorem printedLeavittKOneFormula : PrintedLeavittKOneFormula k 2 :=
  printedLeavittKOneFormula_of_inputs k 2 le_rfl (scalarSurjective k)
    (scalarKernel k)

end LeavittKOneRankTwo
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AryLeavittRankTwo.aryBinaryAlgEquiv
#audit_axioms GroupApproximation.AryLeavittRankTwo.subsingleton_algebraicKOne
#audit_axioms GroupApproximation.LeavittKOneRankTwo.scalarSurjective
#audit_axioms GroupApproximation.LeavittKOneRankTwo.scalarKernel
#audit_axioms GroupApproximation.LeavittKOneRankTwo.printedLeavittKOneFormula
