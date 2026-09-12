import GroupApproximation.Analysis.CollapseDelormeCorona
import GroupApproximation.Analysis.CollapseLambdaCocycle
import GroupApproximation.Sofic.OmegaKazhdanCompression

/-!
# The two halves of the collapse route are about the same representation

Proof-ledger rows `CO.21` and `CO.21b`.  The printed proof of
`thm:projection-collapse` ends by feeding a cocycle to Delorme–Guichardet, and
the corpus now has both halves — but stated against representations built by
different routes, which is why they had not met:

* `CO.21`'s cocycle, `CollapseLambdaCocycle.lambda_cocycle_almost`, is for
  `OmegaIsometryRepresentation.rep A`, the representation an operator-norm
  *almost* representation induces on `K_ω`.  That is the printed
  `π(h) = [Ad U_n(h)]_ω` built from the lifts of `lem:unitarycorona`.
* `CO.21b`'s endpoint, `CollapseDelormeCorona.collapse_contradiction_corona_delorme`,
  is for `coronaRep D`, the representation carried by a
  `KazhdanCompressionRep` bundle over `B_ω`.  That is the packaging every
  fixed-space result — hence `htransport` — is stated in.

`Sofic/OmegaKazhdanCompression.omegaCompressionRep` builds such a bundle *from*
an almost representation, with `pi = piHom A ω hω`.  So the two
representations are not merely isomorphic: after that construction they are
the same map, restricted along the bundle's inclusion `ι`.
`coronaRep_omegaCompressionRep` says so, and it is a `rfl` once the
definitions are unfolded — `omegaRep` is `D.pi` read inside `B_ω`,
`piHom_apply` reads that back as `piOmega`, and `rep` acts by `piOmega`
through `omegaAct`.

That identification is what lets a cocycle proved for one be consumed by the
other, which is the join `CO.04`'s rewiring needs.
-/

namespace GroupApproximation
namespace CollapseRouteJoin

open Filter Matrix Topology
open UltraproductModelConstruction OmegaOperatorUltraproduct
open UltraproductKazhdanProjection OmegaConjugationOperators

noncomputable section

variable {Γ H : Type} [Group Γ] [Group H] (A : OpAlmostRepresentation H)
  (ω : Ultrafilter ℕ)

/-- **The two representations of the collapse route are one map.**

The cocycle of `CO.21` is proved for `OmegaIsometryRepresentation.rep A`, and
the endpoint of `CO.21b` consumes `CollapseDelormeCorona.coronaRep D`.  When
`D` is the bundle that `Sofic/OmegaKazhdanCompression` builds from `A`, the
two agree on the nose along the bundle's inclusion, so a cocycle for the first
is a cocycle for the second. -/
theorem coronaRep_omegaCompressionRep
    (hω : (ω : Filter ℕ) ≤ cofinite) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (iota : Γ →* H) (s : H) (Qs : Finset Γ) (kappa : ℝ)
    (kazhdan : IsKazhdanPair Γ Qs kappa) (S : Finset Γ)
    (hQS : Qs ⊆ S) (hone : (1 : Γ) ∈ S) (hsymm : ∀ γ ∈ S, γ⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hcomp : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ) (γ : Γ) :
    CollapseDelormeCorona.coronaRep A.model ω w hw
        (OmegaKazhdanCompression.omegaCompressionRep ω A hω iota s Qs kappa
          kazhdan S hQS hone hsymm hgen hcomp) γ
      = OmegaIsometryRepresentation.rep A w ω hω hw (iota γ) := by
  apply LinearIsometryEquiv.ext
  intro x
  rfl

end

end CollapseRouteJoin
end GroupApproximation
