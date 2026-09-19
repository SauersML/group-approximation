import GroupApproximation.Sofic.PerfectLampCompressionRadical

/-!
# Theorem C: the exact radical of a perfect-lamp compression wreath product

For a compression wreath product `W = K^(V/Γ) ⋊ V` with a **perfect torsion**
lamp group `K`,

  `Res_MF(W) = K^(V/Γ)`,   hence   `W / Res_MF(W) ≅ V`.

MF approximation forgets the entire lamp group and remembers exactly the
skeleton.  Both halves are cheap once the finite-order collapse endpoint of
`Compression` is in hand: the lamp side is collapse plus perfectness, and the
exactness side is MF-ness of the acting group.  No amalgam theorem is used.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRadicals

open SemidirectProduct MarkedCompression

/-- **Theorem C.**  The MF radical of a compression wreath product with a
perfect torsion lamp group is exactly its lamp subgroup, and its universal
MF-visible quotient is the acting group. -/
def PerfectLampExactRadical : Prop :=
  ∀ (Γ₀ : Type) [Group Γ₀] (β : Γ₀ →* Γ₀) (hβ : Function.Injective β)
    (K₀ : Type) [Group K₀] [DecidableEq (Cosets β hβ)]
    [Countable (WreathV (K := K₀) β hβ)] [Countable (Vertical β hβ)],
    HasKazhdanPropertyT.{0, 0} Γ₀ →
    (∀ k : K₀, ∃ m : ℕ, 0 < m ∧ k ^ m = 1) →
    commutator K₀ = ⊤ →
    (∃ a₀ : Γ₀, a₀ ∉ Set.range β) →
    IsCDEOperatorMF (Vertical β hβ) →
      actualCoronaMFResidual (WreathV (K := K₀) β hβ) =
          (inl : Lamp K₀ (Cosets β hβ) →* WreathV (K := K₀) β hβ).range ∧
        Nonempty ((WreathV (K := K₀) β hβ ⧸
          actualCoronaMFResidual (WreathV (K := K₀) β hβ)) ≃* Vertical β hβ)

theorem manuscriptTheoremC : PerfectLampExactRadical := by
  intro Γ₀ _ β hβ K₀ _ _ _ _ hΓ htor hK hmover hV
  obtain ⟨a₀, ha₀⟩ := hmover
  exact ⟨PerfectLampRadical.actualCoronaMFResidual_eq_lampRange β hβ hΓ htor hK
      ha₀ hV,
    ⟨PerfectLampRadical.universalVisibleQuotientEquiv β hβ hΓ htor hK ha₀ hV⟩⟩

end MFRadicals
end Manuscript
end GroupApproximation
