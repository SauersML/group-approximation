import GroupApproximation.Algebra.WreathSplitQuotient
import GroupApproximation.Sofic.AlternatingLampLiteralPackage
import GroupApproximation.Sofic.AscendingHNNFullTelescopeRadical
import GroupApproximation.Sofic.UniversalVisibleQuotient
import GroupApproximation.Sofic.WitnessVerticalResiduallyFinite

/-!
# The `A₅`-lamp wreath product: the outer inclusion of its exact MF radical

An *exact* MF radical statement `Res_MF(W) = N` has two halves.  The inclusion
`N ≤ Res_MF(W)` is the analytic half — the compression-collapse theorems.  The
reverse inclusion `Res_MF(W) ≤ N` is the *exactness* half, and it is exactly
the statement that the candidate quotient `W ⧸ N` is MF.

For the literal marked group `E` that exactness half is paper-level: it asks
that a symmetric amalgam be MF, which is an external C\*-algebra theorem about
`A *_C A`, recorded as the unproved `operatorMF` field of
`KunThomShulmanDoubleData` and shown non-dischargeable in general in
`Sofic/DoubleInputsMinimal`.

For the `A₅`-lamp wreath product `W_{A₅} = A₅^{(V/Γ)} ⋊ V` of
`Sofic/AlternatingLampLiteralPackage` the situation is different, and that is
what this file records.  Because `A₅` is perfect, the candidate universal MF
quotient is the acting group `V` itself, and `V` is *already proved residually
finite in this repository*, with no external input:
`WitnessVertical.vertical_residuallyFinite` reduces the concrete affine base
modulo odd moduli, where the compressing diagonal `diag(2,2,2,1)` is invertible.
Residual finiteness gives operator-MF (`isOperatorMF_of_residuallyFinite`), and
a homomorphism into a countable MF group kills the MF radical
(`actualCoronaMFResidual_le_ker_of_isCDEOperatorMF`).  So the exactness half is
free here: **no amalgam theorem is used anywhere below.**

## What is proved

* `vertical_isCDEOperatorMF` — the acting group is MF in the literal
  Carrión--Dadarlat--Eckhardt sense;
* `actualCoronaMFResidual_le_ker_rightHom`, `actualCoronaMFResidual_le_lampRange`
  — the **exactness half**: the MF radical of `W_{A₅}` is contained in the lamp
  subgroup, unconditionally;
* `telescopeRadical_le_actualCoronaMFResidual_alternating` — the unconditional
  part of the analytic half, transported from
  `Sofic/AscendingHNNFullTelescopeRadical`;
* `alternatingRadical_sandwich` — the two together;
* `actualCoronaMFResidual_eq_lampRange_iff` — the exact computation
  `Res_MF(W_{A₅}) = A₅^{(V/Γ)}` is now equivalent to the *single* remaining
  inclusion `A₅^{(V/Γ)} ≤ Res_MF(W_{A₅})`.

That last equivalence is the honest statement of the residual gap.  What is
still missing is the passage from the involutive lamp differences of
`telescopeRadical` — the only lamps the unconditional collapse endpoint reaches
— to *every* lamp value, which needs the fibrewise abelianization step
(`TorsionCompressionCollapse.commute_map_of_collapse`) together with
perfectness of `A₅` (`Algebra/PerfectLamp`).  Nothing in this file assumes it.
-/

namespace GroupApproximation
namespace AlternatingLampLiteral

open MarkedCompression ExplicitLinearModel LiteralDoublingWreath

/-! ## The acting group is MF, with no external input -/

/-- The acting group of the `A₅`-lamp construction is MF in the literal
Carrión--Dadarlat--Eckhardt corona sense.  It is residually finite by
`WitnessVertical.vertical_residuallyFinite`, whose proof is the odd-modulus
congruence argument, so this carries no literature dependence. -/
theorem vertical_isCDEOperatorMF :
    IsCDEOperatorMF (Vertical conjD conjD_injective) :=
  (isCDEOperatorMF_iff_isOperatorMF _).mpr WitnessVertical.vertical_isOperatorMF

/-! ## The exactness half of the exact radical -/

/-- **The exactness half, unconditionally.**  Every corona representation of
`W_{A₅}` kills only elements of the kernel of the wreath projection: the
projection lands in an MF group, so it kills the MF radical.  This is the
inclusion that a symmetric-amalgam theorem is needed for in the literal marked
group, and that is free here. -/
theorem actualCoronaMFResidual_le_ker_rightHom :
    actualCoronaMFResidual WA ≤
      (SemidirectProduct.rightHom : WA →* Vertical conjD conjD_injective).ker :=
  actualCoronaMFResidual_le_ker_of_isCDEOperatorMF
    (SemidirectProduct.rightHom : WA →* Vertical conjD conjD_injective)
    vertical_isCDEOperatorMF

/-- The same inclusion read on the lamp subgroup, which is the kernel of the
wreath projection. -/
theorem actualCoronaMFResidual_le_lampRange :
    actualCoronaMFResidual WA ≤
      (SemidirectProduct.inl :
        Lamp (alternatingGroup (Fin 5)) (Cosets conjD conjD_injective) →*
          WA).range :=
  actualCoronaMFResidual_le_ker_rightHom.trans
    (le_of_eq (ker_rightHom_eq_lampRange
      (K := alternatingGroup (Fin 5)) (G := Vertical conjD conjD_injective)
      (X := Cosets conjD conjD_injective)))

/-! ## The analytic half, as far as it is unconditional -/

/-- The equal-height lamp differences of the involution `a₅` lie in the MF
radical.  Property `(T)` of the concrete affine base and the ascending-HNN
relation are the only inputs. -/
theorem telescopeRadical_le_actualCoronaMFResidual_alternating :
    telescopeRadical conjD conjD_injective a5 ≤ actualCoronaMFResidual WA :=
  telescopeRadical_le_actualCoronaMFResidual conjD conjD_injective
    CommutingLampCollapse.gammaBar_hasKazhdanPropertyT a5_mul_self

/-- **The unconditional sandwich.**  The MF radical of the `A₅`-lamp wreath
product contains every equal-height lamp difference of the witness involution
and is contained in the lamp subgroup. -/
theorem alternatingRadical_sandwich :
    telescopeRadical conjD conjD_injective a5 ≤ actualCoronaMFResidual WA ∧
      actualCoronaMFResidual WA ≤
        (SemidirectProduct.inl :
          Lamp (alternatingGroup (Fin 5)) (Cosets conjD conjD_injective) →*
            WA).range :=
  ⟨telescopeRadical_le_actualCoronaMFResidual_alternating,
    actualCoronaMFResidual_le_lampRange⟩

/-! ## The residual gap, stated exactly -/

/-- **The exact computation is now one inclusion away.**  For the `A₅`-lamp
wreath product the identity `Res_MF = A₅^{(V/Γ)}` holds if and only if the lamp
subgroup lies in the MF radical.  The exactness half is discharged above, so
this `Iff` isolates the whole remaining mathematical content in the analytic
direction — and, unlike the literal marked group, no amalgam theorem enters. -/
theorem actualCoronaMFResidual_eq_lampRange_iff :
    actualCoronaMFResidual WA =
        (SemidirectProduct.inl :
          Lamp (alternatingGroup (Fin 5)) (Cosets conjD conjD_injective) →*
            WA).range ↔
      (SemidirectProduct.inl :
        Lamp (alternatingGroup (Fin 5)) (Cosets conjD conjD_injective) →*
          WA).range ≤ actualCoronaMFResidual WA := by
  constructor
  · intro h
    exact le_of_eq h.symm
  · intro h
    exact le_antisymm actualCoronaMFResidual_le_lampRange h

end AlternatingLampLiteral
end GroupApproximation
