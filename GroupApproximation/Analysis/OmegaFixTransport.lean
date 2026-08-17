import GroupApproximation.Analysis.NormalKazhdanUltraproduct
import GroupApproximation.Analysis.OmegaActionLinear
import GroupApproximation.Analysis.OmegaConjugationOperators

/-!
# `Fix π(s ι(Γ) s⁻¹) = Fix π(ι(Γ))` inside `K_ω`

This is the identification the collapse lane carries as the hypothesis
`htransport` of `Analysis/CollapseUltraproductRepresentation.lean`:

> `htransport : ∀ y : KOmega Y w ω hw, (∀ a : H, π (c a) y = y) → ∀ g : H, π g y = y`

that is, every vector fixed by the *compressed* image is fixed by the whole
group.

## Which inclusion is the hard one

Only one of the two inclusions is free, and it is **not** the one `htransport`
needs.

* `Fix π(ι Γ) ⊆ Fix π(s ι(Γ) s⁻¹)` is `kt_19_omega_fix_conjugated`, and it
  consumes nothing but the one-sided compression `s ι(Γ) s⁻¹ ⊆ ι(Γ)`.
* `Fix π(s ι(Γ) s⁻¹) ⊆ Fix π(ι Γ)` is the direction `htransport` asks for, and
  the printed hypothesis does **not** give it directly: one-sided compression is
  one-sided, so there is no reason for a vector fixed by the conjugated image to
  be fixed by the original one.

The printed proof of `\label{thm:kazhdan-transport}` is careful about exactly
this: it derives `ran P = Fix ⊆ V Fix = ran Q`, hence only `P ≤ Q`, and then
spends finiteness of `B_ω` and `\label{lem:finitecompare}` to upgrade that to
`Q = P`.  If the two fixed spaces agreed for free, the entire finiteness step
would be unnecessary.

## The derivation

Three inputs, and each is already proved on the printed objects:

* `Fix π(ι Γ) = ran P` -- the inclusion `ran P ⊆ Fix` is
  `kt_08_rep_mul_proj`, and the reverse `Fix ⊆ ran P` is
  `OmegaActionLinear.omegaAct_proj_of_fixed`, which needed `ℂ`-linearity of
  `omegaAct` in the algebra argument;
* `Fix π(s ι(Γ) s⁻¹) = V · Fix` -- `kt_19_omega_mem_fix_iff`;
* `V P V* = P`, hence `V P = P V` -- `nk_07_commute_proj` at `g = s`, whose
  compression hypothesis is the bundle's own `compresses`, and which consumes
  Dedekind finiteness of `B_ω` (an instance, not an assumption).

So a vector `η` fixed by the conjugated image has `V* η ∈ Fix`, hence
`P (V* η) = V* η`; applying `V` and commuting `P` past it gives `P η = η`; and
`P` absorbs every `π(ι γ)`, so `η` is fixed by the original image.

## Ambient

`KOmega Y w ω hw` is a `def` synonym of `Vec Y w ω`, so the carrier here is the
collapse lane's carrier at the same weight.  The *action* is not the same
construction: this file uses the action of the C-star algebra `B_ω` on `K_ω`
(`omegaAct`), while `CollapseUltraproductRepresentation` builds `conjRep`
directly into `KOmega ≃ₗᵢ[ℂ] KOmega` from a strictly multiplicative coordinate
lift.  Both act by `[ξ_n]_ω ↦ [U_n ξ_n U_n*]_ω`
(`OmegaCommutatorFixes.omegaAct_piOmega_cls`), but only the first carries the
finite C-star ambient the hard inclusion consumes.
-/

namespace GroupApproximation
namespace OmegaFixTransport

open Filter Matrix Topology
open UltraproductModelConstruction OmegaOperatorUltraproduct
open UltraproductKazhdanProjection OmegaConjugationOperators

noncomputable section

section Transport

variable {Γ H : Type} [Group Γ] [Group H]
variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (ω : Ultrafilter ℕ)
  (w : ℕ → ℝ)

/-- **The Kazhdan projection fixes every vector fixed by the conjugated
image.**  This is the whole of the hard inclusion; the rest is absorption. -/
theorem omegaAct_proj_of_fix_conjugated (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) {η : Vec Y w ω}
    (hη : ∀ γ : Γ, omegaAct Y w ω hw
        (omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹)) η = η) :
    omegaAct Y w ω hw D.proj η = η := by
  -- `V P = P V`, from `V P V* = P` and finiteness of `B_ω`
  have hVP : D.shift * D.proj = D.proj * D.shift :=
    NormalKazhdanUltraproduct.nk_07_commute_proj D D.s D.compresses
  -- `V* η` lies in `Fix`, so `P` fixes it
  have hmem : omegaAct Y w ω hw (star D.shift) η ∈ omegaFix Y ω w hw D :=
    (kt_19_omega_mem_fix_iff Y ω w hw D η).1 hη
  have hPζ : omegaAct Y w ω hw D.proj
        (omegaAct Y w ω hw (star D.shift) η)
      = omegaAct Y w ω hw (star D.shift) η :=
    OmegaActionLinear.omegaAct_proj_of_fixed Y w ω hw D
      ((mem_omegaFix_iff Y ω w hw D _).1 hmem)
  -- `V` undoes `V*`
  have hVζ : omegaAct Y w ω hw D.shift
      (omegaAct Y w ω hw (star D.shift) η) = η := by
    rw [← omegaAct_mul, D.shift_mul_star, omegaAct_one]
  calc omegaAct Y w ω hw D.proj η
      = omegaAct Y w ω hw D.proj
          (omegaAct Y w ω hw D.shift
            (omegaAct Y w ω hw (star D.shift) η)) := by rw [hVζ]
    _ = omegaAct Y w ω hw (D.proj * D.shift)
          (omegaAct Y w ω hw (star D.shift) η) := by rw [omegaAct_mul]
    _ = omegaAct Y w ω hw (D.shift * D.proj)
          (omegaAct Y w ω hw (star D.shift) η) := by rw [hVP]
    _ = omegaAct Y w ω hw D.shift
          (omegaAct Y w ω hw D.proj
            (omegaAct Y w ω hw (star D.shift) η)) := by rw [omegaAct_mul]
    _ = omegaAct Y w ω hw D.shift
          (omegaAct Y w ω hw (star D.shift) η) := by rw [hPζ]
    _ = η := hVζ

/-- **`htransport`, the hard inclusion.**  Every vector of `K_ω` fixed by the
conjugated image `π(s ι(Γ) s⁻¹)` is fixed by `π(ι Γ)`.

This is the implication the collapse lane carries as a hypothesis.  It is not
`kt_19_omega_fix_conjugated`, which is the converse and is free; this direction
consumes the Kazhdan projection and Dedekind finiteness of `B_ω`. -/
theorem fix_of_fix_conjugated (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) {η : Vec Y w ω}
    (hη : ∀ γ : Γ, omegaAct Y w ω hw
        (omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹)) η = η) :
    η ∈ omegaFix Y ω w hw D := by
  have hPη : omegaAct Y w ω hw D.proj η = η :=
    omegaAct_proj_of_fix_conjugated Y ω w hw D hη
  have hrepproj : ∀ γ : Γ, omegaRep Y ω D (D.iota γ) * D.proj = D.proj :=
    fun γ ↦ D.kt_08_rep_mul_proj γ
  refine (mem_omegaFix_iff Y ω w hw D η).2 fun γ ↦ ?_
  calc omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ)) η
      = omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ))
          (omegaAct Y w ω hw D.proj η) := by rw [hPη]
    _ = omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ) * D.proj) η := by
        rw [omegaAct_mul]
    _ = omegaAct Y w ω hw D.proj η := by rw [hrepproj]
    _ = η := hPη

/-- **`Fix π(s ι(Γ) s⁻¹) = Fix π(ι Γ)` inside `K_ω`**, as an equivalence of the
two fixing conditions.

The forward direction is the hard one and is `fix_of_fix_conjugated`; the
backward direction is `kt_19_omega_fix_conjugated`, which needs only the
one-sided compression. -/
theorem fix_conjugated_iff (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (η : Vec Y w ω) :
    (∀ γ : Γ, omegaAct Y w ω hw
        (omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹)) η = η)
      ↔ η ∈ omegaFix Y ω w hw D :=
  ⟨fun hη ↦ fix_of_fix_conjugated Y ω w hw D hη,
   fun hη γ ↦ kt_19_omega_fix_conjugated Y ω w hw D hη γ⟩

end Transport

end

end OmegaFixTransport
end GroupApproximation
