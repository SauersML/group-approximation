import GroupApproximation.Analysis.CollapseDelormeEndpoint
import GroupApproximation.Analysis.OmegaFixRange

/-!
# `htransport`, derived rather than assumed

Proof-ledger row `CO.21b`, the third of the four printed clauses in the last
paragraph of the proof of `thm:projection-collapse` in
`non_mf_groups_exist.tex` (navigate by the label; that file is under
concurrent edit):

> The fixed-space comparison gives `Fix π(sLs⁻¹) = Fix π(L)`.

The row records that `collapse_contradiction` and its Delorme companion take
this as the named hypothesis `htransport` rather than deriving it, and it
gives a two-part diagnosis of why `OmegaFixRange.fix_of_fix_conjugated` — which
*is* the printed inference, proved — could not simply be plugged into the
binder: the compression enters the endpoint in one shape and the bundle
supplies it in another, and the representation enters in one shape and the
corona supplies it in another.

Both halves are addressed here, and the hypothesis is discharged.

* **The compression.**  `KazhdanCompressionRep` delivers the printed
  `s ι(Γ) s⁻¹ ⊆ ι(Γ)` as `compresses : ∀ γ, ∃ δ, s ι(γ) s⁻¹ = ι(δ)`.  Choice
  turns that into a map `compressionMap` and into a homomorphism only when `ι`
  is injective, which it is not assumed to be.  The endpoint now takes a plain
  map, so `compressionMap` is exactly what it wants.
* **The representation.**  `htransport` is stated for a family of *linear
  automorphisms*, and that is all the coboundary form of the endpoint uses.
  `coronaEquiv` supplies them: `omegaAct ∘ omegaRep D ∘ ι` is multiplicative
  because `omegaRep` is `D.pi` read inside `B_ω`, so `π(ι γ⁻¹)` inverts
  `π(ι γ)` and no norm estimate is needed.

`collapse_contradiction_corona` is then the printed contradiction with three of
the four clauses supplied and `htransport` **proved**.

## What this does not do

It does not discharge `htransport` in
`collapse_contradiction_of_hasKazhdanPropertyT`.  That form proves the
coboundary from property (T) instead of taking it, and Delorme–Guichardet needs
`π` bundled as `Γ →* (K_ω ≃ₗᵢ[ℂ] K_ω)` — isometries, not merely linear
automorphisms.  The multiplicativity is already here; what is missing is the
norm preservation of `omegaAct (omegaRep D g)` on `K_ω`, which for a general
unitary of `B_ω` is not the coordinatewise computation that
`OmegaIsometryRepresentation.norm_actK` performs for an almost representation.
So the coboundary stays a hypothesis of the statement below, and the row's
Delorme clause is untouched.
-/

namespace GroupApproximation
namespace CollapseTransportEndpoint

open Filter Matrix Topology
open UltraproductModelConstruction OmegaOperatorUltraproduct
open UltraproductKazhdanProjection OmegaConjugationOperators

noncomputable section

variable {Γ H : Type} [Group Γ] [Group H]
variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (ω : Ultrafilter ℕ)
  (w : ℕ → ℝ)

/-! ## `π` read on the Kazhdan source -/

/-- `π` is multiplicative: `omegaRep` is `D.pi` read inside `B_ω`, and both the
representation and the inclusion of the unitary group are multiplicative. -/
theorem omegaRep_mul (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω))
    (g h : H) :
    omegaRep Y ω D (g * h) = omegaRep Y ω D g * omegaRep Y ω D h := by
  have hco : ((D.pi (g * h) : unitary (OmegaAdjointCorona Y ω)) :
        OmegaAdjointCorona Y ω)
      = ((D.pi g : unitary (OmegaAdjointCorona Y ω)) :
          OmegaAdjointCorona Y ω) *
        ((D.pi h : unitary (OmegaAdjointCorona Y ω)) :
          OmegaAdjointCorona Y ω) := by
    rw [map_mul]
    rfl
  exact hco

theorem omegaRep_one (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    omegaRep Y ω D 1 = 1 := by
  have h1 : ((D.pi (1 : H) : unitary (OmegaAdjointCorona Y ω)) :
      OmegaAdjointCorona Y ω) = 1 := by
    rw [map_one]
    rfl
  exact h1

/-- The action of `π(ι γ)` on `K_ω`. -/
def coronaAct (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (γ : Γ) :
    Vec Y w ω →ₗ[ℂ] Vec Y w ω :=
  omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ))

theorem coronaAct_comp_inv (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (γ : Γ) :
    (coronaAct Y ω w hw D γ).comp (coronaAct Y ω w hw D γ⁻¹)
      = LinearMap.id := by
  refine LinearMap.ext fun x ↦ ?_
  show omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ))
      (omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ⁻¹)) x) = x
  rw [← omegaAct_mul, ← omegaRep_mul, ← map_mul D.iota, mul_inv_cancel,
    map_one D.iota, omegaRep_one, omegaAct_one]

theorem coronaAct_inv_comp (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (γ : Γ) :
    (coronaAct Y ω w hw D γ⁻¹).comp (coronaAct Y ω w hw D γ)
      = LinearMap.id := by
  refine LinearMap.ext fun x ↦ ?_
  show omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ⁻¹))
      (omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ)) x) = x
  rw [← omegaAct_mul, ← omegaRep_mul, ← map_mul D.iota, inv_mul_cancel,
    map_one D.iota, omegaRep_one, omegaAct_one]

/-- **`π(ι γ)` as a linear automorphism of `K_ω`**, with `π(ι γ⁻¹)` for its
inverse.  This is all the coboundary form of the collapse endpoint asks of
`π`, and it costs no analysis: the corona action is a ring homomorphism and
`omegaRep ∘ ι` is a group homomorphism into the units. -/
def coronaEquiv (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (γ : Γ) :
    Vec Y w ω ≃ₗ[ℂ] Vec Y w ω :=
  LinearEquiv.ofLinear (coronaAct Y ω w hw D γ) (coronaAct Y ω w hw D γ⁻¹)
    (coronaAct_comp_inv Y ω w hw D γ) (coronaAct_inv_comp Y ω w hw D γ)

@[simp] theorem coronaEquiv_apply (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (γ : Γ)
    (x : Vec Y w ω) :
    coronaEquiv Y ω w hw D γ x
      = omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ)) x := rfl

/-! ## The compression as a map on the source -/

/-- **The printed `γ ↦ sγs⁻¹`, read on the Kazhdan source.**  The bundle
delivers the compression existentially, so this is a choice; it is a
homomorphism only when `ι` is injective, which is not assumed, and that is why
the collapse endpoint takes a plain map for it. -/
def compressionMap
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) : Γ → Γ :=
  fun γ ↦ Classical.choose (D.compresses γ)

theorem iota_compressionMap
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (γ : Γ) :
    D.iota (compressionMap Y ω D γ) = D.s * D.iota γ * D.s⁻¹ :=
  (Classical.choose_spec (D.compresses γ)).symm

/-! ## `htransport` -/

/-- **The printed `Fix π(sLs⁻¹) = Fix π(L)`, in the implication shape the
collapse endpoint consumes, and proved.**

`OmegaFixRange.fix_of_fix_conjugated` is the inference itself — it runs the
range identifications, the finiteness comparison `P = Q` of
`Analysis/OmegaFiniteComparison`, and the return through `kt_08_rep_mul_proj`.
What is done here is only the shape change: the endpoint's `c` is
`compressionMap`, and `iota_compressionMap` turns a hypothesis about
`π(ι (c a))` into one about `π(s ι(a) s⁻¹)`, which is what that theorem
takes. -/
theorem transport_corona (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (y : Vec Y w ω)
    (hy : ∀ a : Γ, coronaEquiv Y ω w hw D (compressionMap Y ω D a) y = y)
    (g : Γ) : coronaEquiv Y ω w hw D g y = y := by
  have hconj : ∀ γ : Γ, omegaAct Y w ω hw
      (omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹)) y = y := by
    intro γ
    have h := hy γ
    rw [coronaEquiv_apply, iota_compressionMap] at h
    exact h
  show omegaAct Y w ω hw (omegaRep Y ω D (D.iota g)) y = y
  exact OmegaFixRange.fix_of_fix_conjugated Y ω w hw D hconj g

/-- **`CO.21b` with `htransport` proved.**

The printed last paragraph, for the corona action of a Kazhdan compression
bundle.  Three of the four clauses are supplied: `hcompressed` is the printed
`d_{sas⁻¹} = 0`, `hne` is the nonvanishing of the previous step, and the
transport is `transport_corona` rather than a hypothesis.  The coboundary
stays a hypothesis here — see the module docstring for exactly what its
Delorme form would still need. -/
theorem collapse_contradiction_corona (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω))
    (β : Γ → Vec Y w ω)
    (hdelorme : ∃ y : Vec Y w ω,
      ∀ g : Γ, β g = y - coronaEquiv Y ω w hw D g y)
    (hcompressed : ∀ a : Γ, β (compressionMap Y ω D a) = 0)
    (hne : ∃ g : Γ, β g ≠ 0) : False :=
  CollapseDelormeEndpoint.collapse_contradiction
    (fun g ↦ coronaEquiv Y ω w hw D g) β (compressionMap Y ω D)
    hdelorme hcompressed
    (fun y hy g ↦ transport_corona Y ω w hw D y hy g) hne

end

end CollapseTransportEndpoint
end GroupApproximation
