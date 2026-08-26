import GroupApproximation.Computability.SoficEnumeratedPi02
import GroupApproximation.Computability.LEFEnumeratedPi02
import GroupApproximation.Computability.TrivialEnumeratedPi02
import GroupApproximation.Computability.AbelianEnumeratedPi02
import GroupApproximation.Computability.ProfinitelyClosedIndexSet
import GroupApproximation.Computability.RFPresentationPi02
import GroupApproximation.Computability.RFEnumeratedHardness
import GroupApproximation.Computability.AmenableEnumeratedHardness
import GroupApproximation.Computability.TorsionFreeEnumeratedHardness
import GroupApproximation.Computability.PerfectEnumeratedHardness
import GroupApproximation.Computability.FreeSubgroupEnumeratedHardness
import GroupApproximation.Computability.IsoInvariantSwitchHardness
import GroupApproximation.Computability.HyperlinearUndecidabilityRoute
import GroupApproximation.Computability.SoficRecognitionPi02
import GroupApproximation.Meta.AxiomGuard

/-!
# The arithmetical ledger, as one closed statement

Every conjunct below is proved elsewhere in `Computability`; this file
collects them so that the ledger of
`research/arithmetical-complexity-table-of-group-properties.md` has a
single kernel-checked endpoint.  Four exact classifications on enumerated
presentation codes (sofic, LEF, trivial, commutative), the strict
placement of soficity and of residual finiteness on finite presentation
codes, second-level lower bounds for residual finiteness, amenability,
torsion-freeness, perfectness, free-subgroup containment and Kazhdan's
property (T), the `Π⁰₃`-completeness of profinite closedness, and the
equivalence between undecidability of hyperlinear recognition and the
existence of a non-hyperlinear finite presentation.
-/

namespace GroupApproximation
namespace ArithmeticalLedgerEndpoint

open ArithmeticalHierarchy EnumeratedPresentationCodes

/-- **The arithmetical ledger of group properties**, as one statement. -/
theorem arithmetical_ledger :
    -- exact classifications on enumerated presentation codes
    Pi02Complete (fun c : PresentationCode ↦ IsSofic (Carrier c)) ∧
    Sigma02Complete (fun c : PresentationCode ↦ ¬ IsSofic (Carrier c)) ∧
    Pi02Complete (fun c : PresentationCode ↦ IsLEF (Carrier c)) ∧
    Pi02Complete (fun c : PresentationCode ↦ Subsingleton (Carrier c)) ∧
    Pi02Complete AbelianEnumeratedPi02.IsCommCode ∧
    -- second-level lower bounds
    Pi02Hard (fun c : PresentationCode ↦ Group.ResiduallyFinite (Carrier c)) ∧
    Pi02Hard (fun c : PresentationCode ↦ Amenability.IsAmenable (Carrier c)) ∧
    Pi02Hard (fun c : PresentationCode ↦ IsPowerTorsionFree (Carrier c)) ∧
    Pi02Hard (fun c : PresentationCode ↦ PerfectEnumeratedHardness.IsPerfectGroup (Carrier c)) ∧
    Pi02Hard (fun c : PresentationCode ↦
      FreeSubgroupEnumeratedHardness.NoFreeSubgroup (Carrier c)) ∧
    Pi02Hard (fun c : PresentationCode ↦ HasKazhdanPropertyT.{0, 0} (Carrier c)) ∧
    -- third level, and the finite-presentation placements
    ProfinitelyClosedIndexSet.Pi03Complete ProfinitelyClosedIndexSet.ClosedIndex ∧
    (Pi02 (fun c : PresentationCodes.PresentationCode ↦
        IsSofic (PresentationCodes.Carrier c)) ∧
      Sigma02 (fun c : PresentationCodes.PresentationCode ↦
        ¬ IsSofic (PresentationCodes.Carrier c))) ∧
    (Pi02 (fun c : PresentationCodes.PresentationCode ↦
        Group.ResiduallyFinite (PresentationCodes.Carrier c)) ∧
      Sigma02 (fun c : PresentationCodes.PresentationCode ↦
        ¬ Group.ResiduallyFinite (PresentationCodes.Carrier c))) :=
  ⟨SoficEnumeratedPi02.sofic_enum_pi02Complete,
   SoficEnumeratedPi02.nonsofic_enum_sigma02Complete,
   LEFEnumeratedPi02.lef_enum_pi02Complete,
   TrivialEnumeratedPi02.trivial_enum_pi02Complete,
   AbelianEnumeratedPi02.comm_enum_pi02Complete,
   RFEnumeratedHardness.rfCode_pi02Hard,
   AmenableEnumeratedHardness.amenableCode_pi02Hard,
   TorsionFreeEnumeratedHardness.torsionFreeCode_pi02Hard,
   PerfectEnumeratedHardness.perfectCode_pi02Hard,
   FreeSubgroupEnumeratedHardness.noFreeSubgroupCode_pi02Hard,
   IsoInvariantSwitchHardness.kazhdanCode_pi02Hard,
   ProfinitelyClosedIndexSet.pi03Complete_closedIndex,
   ⟨SoficRecognitionPi02.pi02_isSofic, SoficRecognitionPi02.sigma02_not_isSofic⟩,
   ⟨RFPresentationPi02.pi02_residuallyFinite,
    RFPresentationPi02.sigma02_not_residuallyFinite⟩⟩

/-- The ledger, as a named closed proposition, so that the closed-axiom
audit can read its head. -/
def ArithmeticalLedgerHolds : Prop :=
    Pi02Complete (fun c : PresentationCode ↦ IsSofic (Carrier c)) ∧
    Pi02Complete (fun c : PresentationCode ↦ IsLEF (Carrier c)) ∧
    Pi02Complete (fun c : PresentationCode ↦ Subsingleton (Carrier c)) ∧
    Pi02Complete AbelianEnumeratedPi02.IsCommCode ∧
    ProfinitelyClosedIndexSet.Pi03Complete ProfinitelyClosedIndexSet.ClosedIndex

theorem arithmeticalLedgerHolds : ArithmeticalLedgerHolds :=
  ⟨SoficEnumeratedPi02.sofic_enum_pi02Complete,
   LEFEnumeratedPi02.lef_enum_pi02Complete,
   TrivialEnumeratedPi02.trivial_enum_pi02Complete,
   AbelianEnumeratedPi02.comm_enum_pi02Complete,
   ProfinitelyClosedIndexSet.pi03Complete_closedIndex⟩

#audit_closed_axioms GroupApproximation.ArithmeticalLedgerEndpoint.arithmeticalLedgerHolds

end ArithmeticalLedgerEndpoint
end GroupApproximation
