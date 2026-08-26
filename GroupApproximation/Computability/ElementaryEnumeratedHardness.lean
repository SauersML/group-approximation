import GroupApproximation.Computability.IsoInvariantSwitchHardness
import GroupApproximation.Computability.BooneGroupFreeBasis
import GroupApproximation.Kazhdan.FreeGroupSharpProfile

/-!
# Finiteness and triviality are second-level hard on enumerated presentations

Two folklore cells of the arithmetical ledger, kernel-checked through the
isomorphism-invariant switch: with the infinite cyclic group as forbidden
seed, "the presented group is finite" and "the presented group is trivial"
are `Π⁰₂`-hard on enumerated presentation codes (research node
`arithmetical-complexity-table-of-group-properties`).
-/

namespace GroupApproximation
namespace ElementaryEnumeratedHardness

open ArithmeticalHierarchy PresentationCodes IsoInvariantSwitchHardness

/-- **Finiteness of enumerated presentation codes is `Π⁰₂`-hard.** -/
theorem finiteCode_pi02Hard :
    Pi02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      Finite (EnumeratedPresentationCodes.Carrier q)) := by
  obtain ⟨seed, ⟨e⟩⟩ := exists_code_mulEquiv (FreeGroup (Fin 1))
  exact enumeratedCodeProperty_pi02Hard (P := fun (H : Type) (_ : Group H) ↦ Finite H)
    { invariant := fun e h ↦ by
        haveI := h
        exact Finite.of_equiv _ e.toEquiv.symm
      trivial := inferInstance
      forbidden := seed
      forbidden_not := fun h ↦ by
        haveI := h
        haveI : Finite (FreeGroup (Fin 1)) := Finite.of_equiv _ e.toEquiv
        exact (Hyperbolic.infinite_freeGroup (Fin 1) ⟨0⟩).not_finite this }

/-- **Triviality of enumerated presentation codes is `Π⁰₂`-hard.** -/
theorem trivialCode_pi02Hard :
    Pi02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      Subsingleton (EnumeratedPresentationCodes.Carrier q)) := by
  obtain ⟨seed, ⟨e⟩⟩ := exists_code_mulEquiv (FreeGroup (Fin 1))
  exact enumeratedCodeProperty_pi02Hard (P := fun (H : Type) (_ : Group H) ↦ Subsingleton H)
    { invariant := fun e h ↦ by
        haveI := h
        exact e.toEquiv.subsingleton
      trivial := inferInstance
      forbidden := seed
      forbidden_not := fun h ↦ by
        haveI := h
        haveI : Subsingleton (FreeGroup (Fin 1)) := e.toEquiv.symm.subsingleton
        exact BooneGroup.FreeBasis.of_ne_one (0 : Fin 1) (Subsingleton.elim _ _) }

end ElementaryEnumeratedHardness
end GroupApproximation
