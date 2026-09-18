-- DRAFT (not landable until B2 and B4 land; names B2/B4 below are anticipated, grep before landing)
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVK2Route.Core
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVUnivLocK2.B5Transfer
-- import …B2Localization   -- provides freeToLeavitt_k2ExactAt : K2ExactAt LVK2Route.freeToLeavitt A
-- import …B4TorsionK1       -- provides [Subsingleton A]

namespace GroupApproximation.Full.LVUnivLocK2

/-- **W1 input, Core-B.**  `K₂(𝔽₂⟨x₀,x₁⟩) → K₂(L_{𝔽₂}(1,2))` is stably onto on finite-stage `K₂`:
exactness of `K₂(R) → K₂(Σ⁻¹R) → K₁(T)` (B2) and `K₁(T) = 0` (B4).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem freeToLeavitt_stableK2BaseSurjective :
    LVStableK2.StableK2BaseSurjective LVK2Route.freeToLeavitt :=
  freeToLeavitt_k2ExactAt.baseSurjective

end GroupApproximation.Full.LVUnivLocK2
