import GroupApproximation.Sofic.SimpleSoficEnvelopeUnconditional

/-!
# Theorem B: a simple sofic MF black hole

Simplicity converts one nonzero invisible element into total invisibility: if
`1 ≠ x ∈ Res_MF(S)` and `S` is simple then `Res_MF(S) = S`, because the radical
is normal.  The work is arranging that while keeping soficity, which is what the
universal sofic envelope does.

The consequence is the striking one: `S` is sofic, and every homomorphism from
`S` to every MF group is trivial.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRadicals

/-- **Theorem B.**  A countable simple sofic group equal to its own MF radical,
so that every homomorphism from it to an MF group is trivial. -/
theorem manuscriptTheoremB :
    ∃ (𝒰 : Ultrafilter ℕ) (X : ℕ → FiniteModel)
      (E : Subgroup (UniversalSofic 𝒰 X)),
      Countable ↥E ∧ IsSimpleGroup ↥E ∧ IsSofic ↥E ∧
        actualCoronaMFResidual ↥E = ⊤ ∧
        (∀ (H : Type) [Group H], IsOperatorMF H →
          ∀ (φ : ↥E →* H) (s : ↥E), φ s = 1) ∧
        ¬ IsOperatorMF ↥E := by
  obtain ⟨U, X, E, hcount, hsimple, hsofic, hcorona, -, hhom, hnot⟩ :=
    SimpleSoficEnvelopeUnconditional.manuscript_simpleSoficEnvelope
  refine ⟨U, X, E, hcount, hsimple, hsofic, ?_, hhom, hnot⟩
  rw [actualCoronaMFResidual_eq_coronaMFResidual]
  exact hcorona

end MFRadicals
end Manuscript
end GroupApproximation
