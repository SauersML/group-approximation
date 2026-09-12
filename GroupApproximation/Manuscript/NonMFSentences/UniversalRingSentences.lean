import GroupApproximation.Leavitt.UniversalOneSidedPairRing
import GroupApproximation.Manuscript.OneSidedMFRadical.UniversalGroupB
import GroupApproximation.Manuscript.NonMFSentences.HeadlineCitationSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# The universal ring `𝒞` in the proof of `thm:full-defect-ring`: the printed reasons

`non_mf_groups_exist.tex`, the proof of Theorem `thm:full-defect-ring`, tex lines
939-943 at origin/main `73c867c5b`:

> The ring `𝒞` is nonzero, since it maps onto `L_{𝔽₂}(1,2)`, and finitely generated,
> so both groups have property (T) by [EJZ, Theorem 1.1], and `EL₄(𝒞)` is finitely
> generated [BHV, Theorem 1.3.1].

`FullDefectRingSentences.manuscriptSentence_finitelyGeneratedPropertyT` carries the
conclusions, but obtains finite generation of `EL₄(𝒞)` from finite generation of the
ring, not along the printed inference "(T) ⇒ finitely generated", and nontriviality of
`𝒞` through a map to `L_{𝔽₂}(1,2)` without the printed surjectivity.  This module
carries both printed reasons:

* `universalToLeavitt` is the unital ring map `𝒞 → L_{𝔽₂}(1,2)`, `sᵢ ↦ sᵢ`, `tᵢ ↦ tᵢ`,
  and `universalToLeavitt_surjective` proves it is onto;
* `manuscriptSentence_universalRingPrintedReasons` derives `𝒞 ≠ 0` from that surjection
  and `EL₄(𝒞)` finitely generated from its property (T) by Bekka–de la Harpe–Valette,
  Theorem 1.3.1, which the repository proves
  (`HeadlineCitationSentences.manuscriptSentence_propertyTGivesFinitelyGenerated`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace UniversalRingSentences

open GroupApproximation.UniversalPair
open GroupApproximation.Manuscript.OneSidedMFRadical

/-- **The printed map `𝒞 → L_{𝔽₂}(1,2)`**: `s₀,s₁,t₀,t₁` to the generators of the
binary Leavitt algebra. -/
noncomputable def universalToLeavitt :
    UniversalPairRing →ₐ[ℤ] BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2) :=
  lift (ofLeavittFamily (BinaryLeavitt.family (ZMod 2)))

/-- **"it maps onto `L_{𝔽₂}(1,2)`"**: the map is surjective. -/
theorem universalToLeavitt_surjective : Function.Surjective universalToLeavitt := by
  intro x
  obtain ⟨y, rfl⟩ :=
    RingQuot.mkAlgHom_surjective (ZMod 2) (BinaryLeavitt.Relation (ZMod 2)) x
  induction y using FreeAlgebra.induction with
  | grade0 c =>
      refine ⟨((ZMod.val c : ℕ) : UniversalPairRing), ?_⟩
      rw [map_natCast, AlgHom.commutes, ← map_natCast (algebraMap (ZMod 2) _) (ZMod.val c),
        ZMod.natCast_zmod_val]
  | grade1 g =>
      refine ⟨gen g, ?_⟩
      simp only [universalToLeavitt, lift_gen]
      fin_cases g <;> rfl
  | mul a b ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' * b', by rw [map_mul, ha', hb', map_mul]⟩
  | add a b ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by rw [map_add, ha', hb', map_add]⟩

/-- **Printed (tex 939-943).**  "The ring `𝒞` is nonzero, since it maps onto
`L_{𝔽₂}(1,2)`, and finitely generated, so both groups have property (T) by
[EJZ, Theorem 1.1], and `EL₄(𝒞)` is finitely generated [BHV, Theorem 1.3.1]." -/
theorem manuscriptSentence_universalRingPrintedReasons :
    Function.Surjective universalToLeavitt ∧
    Nontrivial UniversalPairRing ∧
    IsFinitelyGeneratedRing UniversalPairRing ∧
    HasKazhdanPropertyT.{0, 0} UniversalGroupB.B ∧
    HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin 3) UniversalPairRing) ∧
    Group.FG UniversalGroupB.B :=
  ⟨universalToLeavitt_surjective, universalToLeavitt_surjective.nontrivial,
    isFinitelyGeneratedRing, UniversalGroupB.hasKazhdanPropertyT,
    UniversalGroupB.corner_hasKazhdanPropertyT,
    HeadlineCitationSentences.manuscriptSentence_propertyTGivesFinitelyGenerated
      UniversalGroupB.B UniversalGroupB.hasKazhdanPropertyT⟩

end UniversalRingSentences
end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMFSentences.UniversalRingSentences

#audit_axioms universalToLeavitt_surjective
#audit_closed_axioms manuscriptSentence_universalRingPrintedReasons
