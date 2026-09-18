import GroupApproximation.BooneHigman.Metabelian.ChainWiredFrontier
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeNilLocal
import GroupApproximation.Meta.AxiomGuard

/-!
# The local cube gap wired to the positive-characteristic linear host

Lane `bh-met-46b`.  Module `ElemFPK2CubeNilLocal` reduces the frontier item
`PolyK2OneVarNilStatement` to the local gap `PolyK2CubeNilLocalStatement`.  This module substitutes
that reduction into the consumer `Chain.charPLinearHostStatement_of_frontier` (lane `bh-met-27`).

* `charPLinearHost_of_cubeLocal`: Suslin's theorem, the stable-range diagonal gap, the local cube
  gap and field `K₂` vanishing give `Chain.CharPLinearHostStatement`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- **Endpoint**: the positive-characteristic linear host with the frontier item
`PolyK2OneVarNilStatement` replaced by the local cube gap `PolyK2CubeNilLocalStatement`. -/
theorem charPLinearHost_of_cubeLocal (hS : Absorption.PolynomialSuslinStatement)
    (hdiag : PolyK2StabRangeDiagStatement) (hloc : PolyK2CubeNilLocalStatement)
    (hfield : FieldK2VanishingStatement) : Chain.CharPLinearHostStatement :=
  Chain.charPLinearHostStatement_of_frontier hS hdiag (polyK2OneVarNil_of_cubeLocal hloc) hfield

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.charPLinearHost_of_cubeLocal

end GroupApproximation.BooneHigman.Metabelian.ElemFP
