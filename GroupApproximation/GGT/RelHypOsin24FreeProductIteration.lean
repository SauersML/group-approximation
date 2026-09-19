import GroupApproximation.GGT.RelHypOsin24HullIteration
import GroupApproximation.GGT.RelHypOsin24FreeProductAction

/-!
# Iterated Osin fillings for the Fournier--Facio free product

The free product `U ∗ H` has a concrete relative Hull datum: all of the
`U`-factor is peripheral and a finite Cayley alphabet of the hyperbolic
`H`-factor is the base.  `nonempty_relativeHullData_freeProduct` proves that
this exact alphabet is hyperbolic and acylindrical and that the partner image
is Hull-suitable.

This module combines that initial datum with the finite iteration theorem.
Each target contributes one Hull relator, so finite normal generation of the
kernel follows from the tied one-step quotient construction and composition.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI

/-- Osin's finite-target quotient conclusion for the free-product
configuration used in Fournier--Facio Proposition 2.3. -/
theorem exists_osin24Quotient_freeProduct_of_hull
    (h44family :
      HullSC.HullLemma44CanonicalQuotientFamilyInclusionStatement.{0, 0})
    (h49 : HullSC.HullLemma49KernelPowerStatement.{0, 0})
    (hyi : HullSC.YiSuitablePairAvoidingFiniteOneSided.{0})
    (U H : Type) [Group U] [Group H]
    (hhyp : Hyperbolic.IsHyperbolicGroup H)
    (hsuit : IsSuitableSubgroup
      (fun _ : Unit => freeProductPeripheral U H)
      (MonoidHom.range (freeProductPartnerHom U H)))
    (targets : Set (CoprodI (pairFamily U H))) (htargets : targets.Finite) :
    ∃ (Q : Type) (_ : Group Q)
        (eta : CoprodI (pairFamily U H) →* Q),
      IsOsin24Quotient
          (fun _ : Unit => freeProductPeripheral U H)
          (MonoidHom.range (freeProductPartnerHom U H)) targets Q eta ∧
        eta.ker.IsFinitelyNormallyGenerated := by
  have hrel : IsRelativelyHyperbolic (CoprodI (pairFamily U H))
      (fun _ : Unit => freeProductPeripheral U H) :=
    freeProductRelativelyHyperbolicStatement_proved U H inferInstance
      inferInstance hhyp
  obtain ⟨B⟩ := nonempty_relativeHullData_freeProduct U H hhyp hsuit
  exact exists_osin24Quotient_of_hullContinuation h44family h49 hyi
    (fun _ : Unit => freeProductPeripheral U H) hrel
    (MonoidHom.range (freeProductPartnerHom U H)) hsuit B.toContinuation
    targets htargets

end RelHyp
end GGT
end GroupApproximation
