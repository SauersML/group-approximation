import GroupApproximation.Sofic.Type0Transfer
import GroupApproximation.Sofic.KazhdanSignCriterion

/-!
# The criteria, stated for the groups the manuscript quantifies over

`Sofic/Type0Transfer` supplies the transfer; this file spends it.  The printed
criteria say "let `H` be a countable group", and their formal statements read
`{E : Type}`.  Each corollary below states the printed quantifier and proves it
by moving to the `Type 0` model, applying the narrow theorem there, and
transporting the conclusion back.

The pattern is always the same three steps, and only the data being carried
across the isomorphism changes: transport the homomorphism, the elements and
the hypotheses; apply; transport the conclusion by the property's
isomorphism-invariance.  Nothing here is new mathematics, which is the point --
the ledger marks these rows `MISMATCH` because the transfer was absent from the
development, not because the transfer was doubtful.
-/

namespace GroupApproximation
namespace Type0Corollaries

open CommensurabilityInvariance
open scoped commutatorElement

universe u w

/-- **The central-involution criterion, over any universe.**  The formal
criterion quantifies over ambient groups in `Type 0`; the manuscript quantifies
over countable groups.  A countable group in any universe is isomorphic to one
in `Type 0`, all of the criterion's data transports along that isomorphism, and
being MF is an isomorphism invariant. -/
theorem not_isOperatorMF_of_centralDefectSquare
    {Γ : Type} [Group Γ] {E : Type u} [Group E] [Countable E]
    (hT : HasKazhdanPropertyTComplex.{0, w} Γ)
    (iota : Γ →* E) (t c : E)
    (hcompresses : ∀ γ : Γ, ∃ δ : Γ, t * iota γ * t⁻¹ = iota δ)
    (hcomm : ∀ γ : Γ, Commute c (iota γ))
    (a : Γ) (z : E)
    (hz : z = ⁅t * c * t⁻¹, iota a⁆ ^ 2)
    (hz_ne : z ≠ 1) (hz_sq : z ^ 2 = 1)
    (hz_central : ∀ g : E, Commute z g) :
    ¬ IsOperatorMF E := by
  obtain ⟨E₀, _, ⟨e⟩⟩ := Type0Transfer.exists_type0_model E
  haveI : Countable E₀ := Type0Transfer.countable_type0_model E e
  have key := KazhdanCompressionCore.manuscriptCentralSignCriterion
      (Γ := Γ) (E := E₀) hT (e.toMonoidHom.comp iota) (e t) (e c)
      (fun γ => by
        obtain ⟨δ, hδ⟩ := hcompresses γ
        refine ⟨δ, ?_⟩
        have := congrArg (e : E → E₀) hδ
        simpa [map_mul, map_inv] using this)
      (fun γ => (hcomm γ).map e.toMonoidHom)
      a (e z)
      (by
        have := congrArg (e : E → E₀) hz
        simpa [map_mul, map_inv, map_pow, map_commutatorElement] using this)
      (fun hcon => hz_ne (e.injective (hcon.trans (map_one e).symm)))
      (by rw [← map_pow, hz_sq, map_one])
      (fun g₀ => by
        obtain ⟨g, rfl⟩ := e.surjective g₀
        exact (hz_central g).map e.toMonoidHom)
  have h₀ : ¬ IsOperatorMF E₀ := fun h =>
    key.2 ((isCDEOperatorMF_iff_isOperatorMF _).mpr h)
  exact fun hE => h₀ (isOperatorMF_of_mulEquiv e hE)

end Type0Corollaries
end GroupApproximation
