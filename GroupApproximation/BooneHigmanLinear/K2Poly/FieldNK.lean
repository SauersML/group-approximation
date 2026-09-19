import GroupApproximation.BooneHigmanLinear.K2Poly.FieldZCentral
import GroupApproximation.BooneHigmanLinear.K2Poly.Statements
import GroupApproximation.Meta.AxiomGuard

/-!
# A5 reduced to the coset step A5.2

k2-poly piece A5 (lane bh-pal-wire). With A5.1 proved for every field (`fieldZCentralAt`,
K2Poly/FieldZCentral), the field case `FieldNKStatement` of LSV's Theorem 2.2 needs only
k2-field-a's coset statement `FieldNF.FieldCosetAt F` for every field:

* `fieldStab_of_fieldCoset`: `FieldCosetAt F → FieldStabAt F`;
* `fieldNK_of_fieldCoset`: `(∀ F, FieldCosetAt F) → FieldNKStatement`, through
  `fieldConst_of_fieldStab`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly

/-- `FieldStabAt F` from the coset step alone. -/
theorem fieldStab_of_fieldCoset (F : Type) [Field F] (hC : FieldNF.FieldCosetAt F) :
    FieldStabAt F :=
  FieldNF.fieldStab_of_coset (fieldZCentralAt F) hC

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fieldStab_of_fieldCoset

/-- **A5 from A5.2.** `NK₂` of every field vanishes once the coset step holds at every field. -/
theorem fieldNK_of_fieldCoset (hC : ∀ (F : Type) [Field F], FieldNF.FieldCosetAt F) :
    FieldNKStatement := fun F _ _ hr =>
  fieldConst_of_fieldStab (fieldStab_of_fieldCoset F (hC F)) (by omega)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fieldNK_of_fieldCoset

end GroupApproximation.BooneHigmanLinear.K2Poly
