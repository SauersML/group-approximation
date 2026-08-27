import GroupApproximation.Sofic.SingleDefectSaturation
import GroupApproximation.Sofic.LiteralAffineCongruenceSource

/-!
# The arithmetic single-defect construction, at its own source

`SingleDefectSaturation` is generic: it says what follows for *any* compression
source once a router saturates one marked defect element.  This file pins it to
the concrete arithmetic source and states the construction as a single theorem,
so that exactly one hypothesis is left standing and it is visible in the
statement.

The source is `LiteralAffineCongruenceSource`: the base is
`P = ℤ³ ⋊ Γ(3)` (as the level-three subgroup `↑levelThree` of the literal
affine base), the compression is the affine map doubling translations and
fixing the level-three linear part, the omitted element is the first
translation, and the envelope is the resulting HNN extension.  Everything about
that source is already proved with no hypotheses at all --- torsion-freeness of
the base by Minkowski at level three, finite presentation through
Reidemeister--Schreier, property `(T)` from the `SL₃(ℤ)` certificate carried
across finite index, torsion-freeness and finite presentation of the envelope,
and nontriviality of the marked commutator by Britton's lemma.

## What is left, precisely

Both theorems below take one argument:
`Nonempty (SingleDefectRouterData arithmeticSource)`.  That is the
acylindrically hyperbolic small-cancellation step --- a common quotient of the
envelope and a property-`(T)` partner, finitely presented, torsion-free,
two-generated, in which the image of one prescribed element normally generates.
Mathlib has no acylindrical hyperbolicity, no hyperbolically embedded
subgroups, and no rotating families, so that step cannot be built here and is
**not** claimed.  The `_of_singleDefectRouter` suffix is part of the name for
the same reason it is part of
`exists_nontrivial_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical_of_bareRoutingData`:
neither may be cited as an unconditional existence theorem.

What this file does buy is that the hypothesis is now a *single, named, minimal*
one, attached to a *concrete* source rather than to an arbitrary datum.  The
router has to saturate one explicitly written commutator in one explicitly
written group; it does not have to preserve a distinguished subgroup, and no
simple factor or simplicity-protection argument appears anywhere in the chain.
-/

namespace GroupApproximation
namespace ArithmeticSingleDefectEndpoint

open LiteralAffineCongruenceBase
open LiteralAffineCongruenceSource
open SingleDefectSaturation
open BareFullMFRadicalEndpoint

noncomputable section

/-- **The arithmetic compression source.**  `ℤ³ ⋊ Γ(3)` compressed by affine
translation-doubling, inside its HNN envelope.  Premise-free: this is
`LiteralAffineCongruenceSource.literalBareDefectSourceData` under a name that
says which construction consumes it. -/
noncomputable abbrev arithmeticSource :
    BareDefectSourceData P Envelope :=
  literalBareDefectSourceData

/-- **The one element a router has to saturate.**  The marked commutator of the
arithmetic source, `[t c t⁻¹, ι(v₁)]`. -/
noncomputable def arithmeticMarkedCommutator : Envelope :=
  markedCommutator arithmeticSource

/-- The marked element is a compression defect, by the generating clause of the
compression core. -/
theorem arithmeticMarkedCommutator_mem_defectNormal :
    arithmeticMarkedCommutator ∈ arithmeticSource.core.defectNormal :=
  markedCommutator_mem_defectNormal arithmeticSource

/-- The marked element is nontrivial in the envelope.  This is Britton's lemma
on the arithmetic source, already proved there with no hypotheses. -/
theorem arithmeticMarkedCommutator_ne_one : arithmeticMarkedCommutator ≠ 1 :=
  markedCommutator_ne_one arithmeticSource

/-- **The construction, with its single remaining hypothesis.**

Supply a router that makes the image of the one marked commutator normally
generate its quotient, and the quotient is a nontrivial, countable,
two-generated, finitely presented, torsion-free, property-`(T)` group equal to
its own literal CDE MF radical.

Every other input is discharged inside Lean: the source is the concrete
arithmetic one, its property `(T)` and torsion-freeness are proved, the marked
commutator is nontrivial by Britton, and saturation upgrades that single
element to the whole compression defect.

The router is a hypothesis and is not constructed here. -/
theorem exists_twoGenerated_torsionFree_fullMFRadical_of_singleDefectRouter
    (h : Nonempty (SingleDefectRouterData arithmeticSource)) :
    ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
      IsTwoGenerated Q ∧
      Group.IsFinitelyPresented Q ∧
      IsPowerTorsionFree Q ∧
      HasKazhdanPropertyT.{0, 0} Q ∧
      Nontrivial Q ∧
      cdeMFResidual Q = ⊤ :=
  exists_nontrivial_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical_of_bareRoutingData
    (nonempty_bareRoutingData_of_singleDefect h)

/-- **The hereditary half, at the same source.**  From the same single router
hypothesis, every genuine norm-matrix-corona representation of the routed group
is trivial and every nontrivial quotient again fails to be MF: the obstruction
is not merely present, it survives every further quotient. -/
theorem exists_every_nontrivial_quotient_not_isCDEOperatorMF_of_singleDefectRouter
    (h : Nonempty (SingleDefectRouterData arithmeticSource)) :
    ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
      IsTwoGenerated Q ∧
      Group.IsFinitelyPresented Q ∧
      IsPowerTorsionFree Q ∧
      HasKazhdanPropertyT.{0, 0} Q ∧
      Nontrivial Q ∧
      ¬ IsCDEOperatorMF Q ∧
      (∀ (X : ℕ → FiniteModel) (hne : ∀ n, Nonempty (X n)),
        letI := hne
        (∀ n, 0 < Fintype.card (X n)) →
          ∀ rho : Q →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
            rho = 1) ∧
      ∀ (H : Type) (_ : Group H) (_ : Countable H) (_ : Nontrivial H)
        (f : Q →* H),
        Function.Surjective f → ¬ IsCDEOperatorMF H :=
  exists_nontrivial_group_with_every_nontrivial_quotient_not_isCDEOperatorMF_of_bareRoutingData
    (nonempty_bareRoutingData_of_singleDefect h)

end

end ArithmeticSingleDefectEndpoint
end GroupApproximation
