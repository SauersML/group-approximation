import GroupApproximation.Analysis.CollapseCoronaIsometry
import GroupApproximation.Analysis.CollapseTransportEndpoint
import GroupApproximation.Analysis.OmegaHilbertComplete

/-!
# The printed last paragraph, with nothing left as a hypothesis but the cocycle

Proof-ledger row `CO.21b`.  The printed paragraph has four clauses —
Delorme–Guichardet makes `β` a coboundary, the hypothesis on `p` fixes the
primitive under the compressed subgroup, the fixed-space comparison identifies
the two fixed spaces, and the contradiction follows — and the row has tracked
which of them were assumed rather than proved.

They are all proved now, for the corona action of a Kazhdan compression
bundle.

* `Analysis/CollapseTransportEndpoint` derived `htransport` from
  `OmegaFixRange.fix_of_fix_conjugated`, but only for the *coboundary* form of
  the endpoint, which takes the primitive as a hypothesis.  The Delorme form
  produces the primitive from property (T), and it consumes `π` as a
  homomorphism into the **isometries** of `K_ω`.
* `Analysis/CollapseCoronaIsometry` supplied the missing analytic fact: a
  unitary of `B_ω` acts on `K_ω` by an isometry.
* `coronaIsometryEquiv` and `coronaRep` bundle the two — the multiplicativity
  was already free, since `omegaRep` is `D.pi` read inside `B_ω` — and
  `collapse_contradiction_corona_delorme` is the printed paragraph with
  Delorme–Guichardet proved, the transport proved, and completeness of `K_ω`
  found by instance search from `Analysis/OmegaHilbertComplete`.

What remains a hypothesis is the *cocycle*: `β` and its identity
`β(gh) = β(g) + π(g) β(h)` come from the previous printed step, which is
`CO.21`, and are supplied there by `CollapseLambdaCocycle.lambda_cocycle`.
Joining the two across the corona quotient is the wiring `CO.04` asks for and
is not done here.
-/

namespace GroupApproximation
namespace CollapseDelormeCorona

open Filter Matrix Topology
open UltraproductModelConstruction OmegaOperatorUltraproduct
open UltraproductKazhdanProjection OmegaConjugationOperators
open KOmegaHilbert CollapseCoronaIsometry CollapseTransportEndpoint

noncomputable section

variable {Γ H : Type} [Group Γ] [Group H]
variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (ω : Ultrafilter ℕ)
  (w : ℕ → ℝ)

/-- The value of `π` at any group element is a unitary of `B_ω`: that is what
the bundle's `pi` field says. -/
theorem omegaRep_mem_unitary
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (g : H) :
    omegaRep Y ω D g ∈ unitary (OmegaAdjointCorona Y ω) := (D.pi g).2

/-- **`π(ι γ)` as a unitary of `K_ω`.**  The linear automorphism of
`Analysis/CollapseTransportEndpoint`, now known to preserve the norm. -/
def coronaIsometryEquiv (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (γ : Γ) :
    KOmega Y w ω hw ≃ₗᵢ[ℂ] KOmega Y w ω hw where
  toLinearEquiv := coronaEquiv Y ω w hw D γ
  norm_map' x := by
    show ‖actKOmega Y w ω hw (omegaRep Y ω D (D.iota γ)) x‖ = ‖x‖
    exact norm_actKOmega_of_unitary Y w ω hw
      (omegaRep_mem_unitary Y ω D (D.iota γ)) x

/-- **The corona representation of the Kazhdan source on `K_ω`**, bundled in
the shape Delorme–Guichardet consumes. -/
def coronaRep (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    Γ →* (KOmega Y w ω hw ≃ₗᵢ[ℂ] KOmega Y w ω hw) where
  toFun γ := coronaIsometryEquiv Y ω w hw D γ
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    show omegaAct Y w ω hw (omegaRep Y ω D (D.iota 1)) x = x
    rw [map_one D.iota, omegaRep_one, omegaAct_one]
  map_mul' γ δ := by
    apply LinearIsometryEquiv.ext
    intro x
    show omegaAct Y w ω hw (omegaRep Y ω D (D.iota (γ * δ))) x
      = omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ))
          (omegaAct Y w ω hw (omegaRep Y ω D (D.iota δ)) x)
    rw [map_mul D.iota, omegaRep_mul, omegaAct_mul]

@[simp] theorem coronaRep_apply (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (γ : Γ)
    (x : KOmega Y w ω hw) :
    coronaRep Y ω w hw D γ x
      = omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ)) x := rfl

/-- **`CO.21b`: the printed last paragraph, with only the cocycle assumed.**

Delorme–Guichardet is proved rather than cited, through
`CollapseDelormeEndpoint.exists_primitive_of_hasKazhdanPropertyT`; completeness
of `K_ω` is proved rather than assumed, and is found by instance search;
`htransport` is proved rather than assumed, through `transport_corona` and
hence through `OmegaFixRange.fix_of_fix_conjugated`; and `π` is built rather
than hypothesised.

`hcompressed` is the printed `d_{sas⁻¹} = 0` and `hne` is the nonvanishing of
the previous step; `hβ` is the cocycle identity of `CO.21`, supplied there by
`CollapseLambdaCocycle.lambda_cocycle`. -/
theorem collapse_contradiction_corona_delorme (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω))
    (hT : HasKazhdanPropertyT.{0, 0} Γ) (β : Γ → KOmega Y w ω hw)
    (hβ : ∀ g h : Γ, β (g * h) = β g + coronaRep Y ω w hw D g (β h))
    (hcompressed : ∀ a : Γ, β (compressionMap Y ω D a) = 0)
    (hne : ∃ g : Γ, β g ≠ 0) : False :=
  CollapseDelormeEndpoint.collapse_contradiction_of_hasKazhdanPropertyT hT
    (coronaRep Y ω w hw D) β (compressionMap Y ω D) hβ hcompressed
    (fun y hy g ↦ transport_corona Y ω w hw D y hy g) hne

end

end CollapseDelormeCorona
end GroupApproximation
