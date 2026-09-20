import GroupApproximation.BooneHigmanLinear.CharZero.BTri.DomainStabilizer
import GroupApproximation.BooneHigmanLinear.CharZero.BTri.Develop
import GroupApproximation.Meta.AxiomGuard

/-!
# Geometric inputs to the one-prime step

The standard vertex stabilizer is proved in `DomainStabilizer`. The outstanding geometric
inputs are the triangle action and simple connectivity. This interface is independent of the
arithmetic finite-generation argument consuming it in `StepWire`.
-/

namespace GroupApproximation.BooneHigmanLinear.BTri

/-- The building inputs at `A` and `p`. -/
structure StepInputs (A : Type) [CommRing A] (p : A) : Prop where
  triangle : ∃ τ : Vertex A (Localization.Away p) p → Fin 3,
    TriangleAction (Matrix.SpecialLinearGroup (Fin 3) (Localization.Away p))
      (buildingGraph A (Localization.Away p) p) (stdVertex A p) τ
  connected : (buildingGraph A (Localization.Away p) p).Connected
  simplyConnected : TriSimplyConnected (buildingGraph A (Localization.Away p) p) (stdVertex A p 0)
  stab : ∀ γ : Matrix.SpecialLinearGroup (Fin 3) (Localization.Away p),
    γ • stdVertex A p 0 = stdVertex A p 0 ↔
      ∀ k l, (γ : Matrix (Fin 3) (Fin 3) (Localization.Away p)) k l ∈
        Set.range (algebraMap A (Localization.Away p))

#audit_axioms StepInputs

/-- The building inputs for every principal ideal domain and prime. -/
def BuildingInputsStatement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] (p : A), Prime p →
    StepInputs A p

#audit_axioms BuildingInputsStatement

/-- The building inputs from the triangle action and simple connectivity. The stabilizer
condition is supplied by `stabilizer_std_zero`. -/
theorem buildingInputs_of (hsc : BuildingSimplyConnectedStatement)
    (hT : ∀ (A : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] (p : A), Prime p →
      ∃ τ : Vertex A (Localization.Away p) p → Fin 3,
        TriangleAction (Matrix.SpecialLinearGroup (Fin 3) (Localization.Away p))
          (buildingGraph A (Localization.Away p) p) (stdVertex A p) τ) :
    BuildingInputsStatement := fun A _ _ _ p hp =>
  ⟨hT A p hp, (hsc A p hp).1, (hsc A p hp).2, stabilizer_std_zero hp⟩

#audit_axioms buildingInputs_of

end GroupApproximation.BooneHigmanLinear.BTri
