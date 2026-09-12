import GroupApproximation.Computability.SoficRecognitionSecondLevel
import GroupApproximation.Sofic.SoficByAmenablePermanence
import GroupApproximation.Sofic.SoficPositiveControl

/-!
# Amenability is second-level hard on enumerated presentations

Amenability passes to subgroups, holds for the trivial group, and fails for
the finitely presented nonsofic group (amenable groups are sofic, by the
sofic-by-amenable permanence theorem applied to the identity).  So the
hereditary switch of `Computability.SoficRecognitionSecondLevel` makes
amenability of enumerated presentation codes `Π⁰₂`-hard and
non-amenability `Σ⁰₂`-hard.  The matching upper bound (Kesten's return
probability criterion) is paper-level: research node
`amenability-two-generator-recursive-is-pi2-complete`.
-/

namespace GroupApproximation
namespace AmenableEnumeratedHardness

open PresentationCodes SoficRecognitionSecondLevel

/-- Amenable groups are sofic: apply sofic-by-amenable permanence to the
identity map, whose kernel is trivial. -/
theorem isSofic_of_isAmenable {G : Type} [Group G]
    (hG : Amenability.IsAmenable G) : IsSofic G := by
  haveI : Subsingleton ((MonoidHom.id G).ker) :=
    ⟨fun a b => Subtype.ext (by
      have ha := a.2
      have hb := b.2
      simp only [MonoidHom.mem_ker, MonoidHom.id_apply] at ha hb
      rw [ha, hb])⟩
  haveI : Finite ((MonoidHom.id G).ker) := Finite.of_subsingleton
  exact SoficByAmenablePermanence.isSofic_of_isSofic_ker_of_isAmenable (MonoidHom.id G)
    Function.surjective_id (isSofic_of_finite' _) hG

/-- Amenability passes to subgroups, hence along injective homomorphisms. -/
theorem isAmenable_of_injective {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (hB : Amenability.IsAmenable B) :
    Amenability.IsAmenable A :=
  SoficByAmenablePermanence.isAmenable_of_mulEquiv (MonoidHom.ofInjective hf)
    (hB.subgroup f.range)

/-- **Amenability of enumerated presentation codes is `Π⁰₂`-hard.** -/
theorem amenableCode_pi02Hard :
    ArithmeticalHierarchy.Pi02Hard
      (fun q : EnumeratedPresentationCodes.PresentationCode ↦
        Amenability.IsAmenable (EnumeratedPresentationCodes.Carrier q)) := by
  obtain ⟨seed, hseed⟩ := exists_nonsofic_presentationCode
  exact pi02Hard_of_hereditary (fun (H : Type) (_ : Group H) ↦ Amenability.IsAmenable H)
    (fun f hf hK ↦ isAmenable_of_injective f hf hK)
    (Amenability.isAmenable_of_finite PUnit) seed
    (fun hA ↦ hseed (isSofic_of_isAmenable hA))

/-- **Non-amenability of enumerated presentation codes is `Σ⁰₂`-hard.** -/
theorem nonamenableCode_sigma02Hard :
    ArithmeticalHierarchy.Sigma02Hard
      (fun q : EnumeratedPresentationCodes.PresentationCode ↦
        ¬ Amenability.IsAmenable (EnumeratedPresentationCodes.Carrier q)) := by
  obtain ⟨seed, hseed⟩ := exists_nonsofic_presentationCode
  exact sigma02Hard_of_hereditary (fun (H : Type) (_ : Group H) ↦ Amenability.IsAmenable H)
    (fun f hf hK ↦ isAmenable_of_injective f hf hK)
    (Amenability.isAmenable_of_finite PUnit) seed
    (fun hA ↦ hseed (isSofic_of_isAmenable hA))

end AmenableEnumeratedHardness
end GroupApproximation
