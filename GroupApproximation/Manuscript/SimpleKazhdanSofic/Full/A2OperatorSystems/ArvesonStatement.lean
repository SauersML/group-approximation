import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2OperatorSystems.MatrixArveson
import GroupApproximation.Meta.AxiomGuard

/-!
# Arveson's extension theorem for matrix targets, order-free and closed (table row A2)

`simple_kazhdan_sofic_group.tex`, tex l.54–56 (table row A2).  The theorem
`exists_ucp_extension_of_system` of `MatrixArveson.lean` carries order binders on `A`, because the
order on `CStarMatrix` needs them.  Here they are supplied by the spectral order
(`CStarAlgebra.spectralOrder`), giving

* `exists_ucp_extension_of_system'`: the same extension with no order binders;
* `operatorSystemMatrixArvesonStatement_holds`: the closed proposition
  `Full.A2LocalLifting.OperatorSystemMatrixArvesonStatement` (Ozawa, *About the QWEP conjecture*,
  Theorem 2.2, ucp case into `B(ℂᵏ)`), proved.
-/

namespace GroupApproximation
namespace Full
namespace A2OperatorSystems

open CStarExactness
open GroupApproximation.Full.A2LocalLifting

universe u

/-- **Arveson extension into `B(ℂᵏ)` from an operator system, order-free** (Ozawa, Theorem 2.2;
table row A2, tex l.54–56).  The order on `A` is the spectral order. -/
theorem exists_ucp_extension_of_system' {A : Type u} [CStarAlgebra A]
    {E : Submodule ℂ A} (hE : IsOperatorSystem E) {k : ℕ}
    (ψ : E →ₗ[ℂ] (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)))
    (hψ : IsCompletelyPositiveOn E ψ)
    (hψ1 : ∀ x : E, (x : A) = 1 → ψ x = 1) :
    ∃ Ψ : A →ₗ[ℂ] (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)),
      IsCompletelyPositive Ψ ∧ Ψ 1 = 1 ∧ ∀ x : E, Ψ (x : A) = ψ x := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact exists_ucp_extension_of_system hE ψ hψ hψ1

/-- **Arveson's extension theorem for matrix targets** (Ozawa, *About the QWEP conjecture*,
Theorem 2.2, the ucp case; table row A2, tex l.54–56), proved: every unital completely positive map
from an operator system into `B(ℂᵏ)` extends to a unital completely positive map on the whole
algebra. -/
theorem operatorSystemMatrixArvesonStatement_holds :
    OperatorSystemMatrixArvesonStatement.{u} := by
  intro B _ E hE k ψ hψ hψ1
  exact exists_ucp_extension_of_system' hE ψ hψ hψ1

end A2OperatorSystems
end Full
end GroupApproximation

open GroupApproximation.Full.A2OperatorSystems in
#audit_axioms exists_ucp_extension_of_system'

open GroupApproximation.Full.A2OperatorSystems in
#audit_closed_axioms operatorSystemMatrixArvesonStatement_holds
