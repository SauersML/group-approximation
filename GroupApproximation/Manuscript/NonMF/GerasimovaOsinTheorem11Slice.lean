import GroupApproximation.Manuscript.NonMF.RegularNonMFAlgebra
import GroupApproximation.Analysis.GroupVonNeumannTrace
import GroupApproximation.Meta.AxiomGuard

/-!
# Gerasimova--Osin, Theorem 1.1: the citation split along their own proof

`cor:regular-nonmf-algebra` cites Gerasimova and Osin for *"density of the
invertible elements, which is stable rank one"*.  Their Theorem 1.1, verbatim
from arXiv:1910.14524v2, reads

> **Theorem 1.1.**  Let `G₁, …, G_k` be acylindrically hyperbolic groups with
> `K(G_i) = {1}` for all `1 ≤ i ≤ k`.  Then `sr(C*_r(G₁ × ⋯ × G_k)) = 1`.  In
> particular, the reduced `C*`-algebra of any acylindrically hyperbolic group
> with trivial finite radical has stable rank `1`.

The manuscript uses the `k = 1` clause, which is `GerasimovaOsinTheorem11Printed`.

## A correction to the route this repository recorded

It has been recorded here that Gerasimova--Osin go through
Dykema--Haagerup--Rørdam.  **They do not.**  Their §5 applies

> **Theorem 5.4 ([DH, Theorem 1.4]).**  Suppose that for any finite subset `F`
> of a group `G`, there exists `t ∈ G` such that `tF` generates a free
> subsemigroup and every `a ∈ ℂG` with `supp(a) ⊆ tF` has the `ℓ²`-spectral
> radius property.  Then `sr(C*_r(G)) = 1`.

with `[DH]` = K. Dykema and P. de la Harpe, *Some groups whose reduced
`C*`-algebras have stable rank one*, J. Math. Pures Appl. **78** (1999), no. 6,
591--608.  No Powers averaging occurs anywhere in their argument, and the
Dykema--Haagerup--Rørdam paper on free products is not cited for this step.

The two hypotheses of Theorem 5.4 are supplied by their own §§2 and 4:

> **Proposition 2.4.**  Let `G` carry a pseudolength function `ℓ` and let
> `S ⊆ G`.  Suppose there is a symmetric `G`-equivariant generalized combing
> `C : G × G → 𝒫(G)` with `C(1,s) ∩ C(s,g) ∩ C(1,g) ≠ ∅` for all `s ∈ S`,
> `g ∈ G`, whose growth functions `γ`, `ρ` are finite.  Then for every
> `a ∈ ℂG` and `n` with `supp(a) ⊆ S ∩ B(n)`,
> `‖a‖ ≤ γ(ρ(n))^{3/2} ‖a‖₂`.

> **Proposition 4.1.**  Let `G` be acylindrically hyperbolic with trivial finite
> radical and `F` a non-empty finite subset.  Then there are a length function
> `ℓ`, an element `t ∈ G`, and a symmetric `G`-equivariant generalized combing
> `C` such that `tF` freely generates a free subsemigroup `S`, the triangle
> condition holds on `S`, and `γ`, `ρ` are bounded above by a linear function.

## What this module does

It names **one** analytic citation, `DykemaDeLaHarpeTheorem14`, over C⋆-algebra
and group vocabulary only, and **one** geometric obligation,
`GerasimovaOsinFreeSubsemigroupInput`, which is Propositions 2.4 and 4.1
combined into the statement Theorem 5.4 consumes.  `gerasimovaOsinTheorem11Printed_of_inputs`
assembles the printed citation from the two.

Splitting a citation is not proving it.  What the split buys is that the first
half is a theorem about reduced group C⋆-algebras with no hyperbolic geometry in
it, and the second is a statement about a group with no operator algebra in it,
so the two can be attacked by different means.

## Vocabulary, and how faithful it is

* *`ℓ²`-norm.*  Gerasimova and Osin write `‖a‖₂` for the `ℓ²`-norm of
  `a ∈ ℂG ⊆ ℓ²(G)`.  Here `reducedTwoNorm a = ‖a δ₁‖`, the norm in `ℓ²(G)` of
  the image of the identity point mass, which is that vector.
* *Spectral radii.*  `r(a) = lim ‖aᵏ‖^{1/k}` and
  `r₂(a) = limsup ‖aᵏ‖₂^{1/k}`; the `ℓ²`-spectral radius property is
  `r₂(a) = r(a)`.  Both are written as `limsup` below: the first limit exists
  (Gelfand), so its `limsup` is its value, and the equality asserted is the
  same one.
* *Support.*  `a ∈ ℂG` with `supp(a) ⊆ T` is transcribed as *a finite `ℂ`-linear
  combination of `λ(γ)` with every `γ ∈ T`*.  Those are exactly the elements of
  the image of `ℂG` in `C*_r(G)` supported in `T`.
* *Free subsemigroup.*  `T` freely generates a free subsemigroup when distinct
  nonempty words in `T` have distinct products.

## Manuscript status

Reduction step for `cor:regular-nonmf-algebra`; certifies no printed sentence on
its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.ReducedGroupCStarTrace
open Filter

universe u

/-! ## The `ℓ²`-norm and the two spectral radii -/

/-- **The `ℓ²`-norm of an element of `C*_r(G)`**: the norm in `ℓ²(G)` of the
image of the identity point mass.  For `a ∈ ℂG` this is
`(∑_g |a_g|²)^{1/2}`, which is what Gerasimova and Osin write `‖a‖₂`. -/
noncomputable def reducedTwoNorm {G : Type u} [Group G] (x : ReducedGroupCStar G) : ℝ :=
  ‖(x : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)‖

/-- **The `ℓ²`-norm is dominated by the operator norm.**

`‖a‖₂ = ‖a δ₁‖ ≤ ‖a‖ ‖δ₁‖ = ‖a‖`.  Consequently the `ℓ²`-spectral radius
property is one inequality, `r(a) ≤ r₂(a)`, and not two: the reverse always
holds termwise. -/
theorem reducedTwoNorm_le_norm {G : Type u} [Group G] (x : ReducedGroupCStar G) :
    reducedTwoNorm x ≤ ‖x‖ := by
  have h : ‖(x : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)‖
      ≤ ‖(x : GroupHilbert G →L[ℂ] GroupHilbert G)‖ * ‖deltaOne G‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [GroupVonNeumann.norm_deltaOne G, mul_one] at h
  -- the norm of `C*_r(G)` is the ambient operator norm, definitionally
  exact h

theorem reducedTwoNorm_nonneg {G : Type u} [Group G] (x : ReducedGroupCStar G) :
    0 ≤ reducedTwoNorm x := norm_nonneg _

/-- **The two spectral radii are computed from termwise comparable numbers.**

`‖aᵏ‖₂^{1/k} ≤ ‖aᵏ‖^{1/k}` for every `k`, so `r₂(a) ≤ r(a)` always and the
`ℓ²`-spectral radius property is the single inequality `r(a) ≤ r₂(a)`. -/
theorem reducedTwoNorm_pow_rpow_le {G : Type u} [Group G]
    (x : ReducedGroupCStar G) (k : ℕ) :
    reducedTwoNorm (x ^ k) ^ ((k : ℝ)⁻¹) ≤ ‖x ^ k‖ ^ ((k : ℝ)⁻¹) :=
  Real.rpow_le_rpow (reducedTwoNorm_nonneg _) (reducedTwoNorm_le_norm _)
    (by positivity)

/-- **The `ℓ²`-spectral radius**, `r₂(a) = limsup ‖aᵏ‖₂^{1/k}`. -/
noncomputable def l2SpectralRadius {G : Type u} [Group G] (x : ReducedGroupCStar G) : ℝ :=
  limsup (fun k : ℕ ↦ reducedTwoNorm (x ^ k) ^ ((k : ℝ)⁻¹)) atTop

/-- **The spectral radius**, `r(a) = lim ‖aᵏ‖^{1/k}`, written as a `limsup`;
the limit exists, so the two agree. -/
noncomputable def operatorSpectralRadius {G : Type u} [Group G]
    (x : ReducedGroupCStar G) : ℝ :=
  limsup (fun k : ℕ ↦ ‖x ^ k‖ ^ ((k : ℝ)⁻¹)) atTop

/-- **The `ℓ²`-spectral radius property** of Dykema and de la Harpe:
`r₂(a) = r(a)`. -/
def HasL2SpectralRadiusProperty {G : Type u} [Group G] (x : ReducedGroupCStar G) : Prop :=
  l2SpectralRadius x = operatorSpectralRadius x

/-! ## Free subsemigroups and supports -/

/-- **`T` freely generates a free subsemigroup**: distinct nonempty words in `T`
have distinct products. -/
def FreelyGeneratesFreeSubsemigroup {G : Type u} [Group G] (T : Set G) : Prop :=
  ∀ w w' : List G, (∀ x ∈ w, x ∈ T) → (∀ x ∈ w', x ∈ T) →
    w ≠ [] → w' ≠ [] → w.prod = w'.prod → w = w'

/-- **Every element of `ℂG` supported in `T` has the `ℓ²`-spectral radius
property.**  Elements of `ℂG` supported in `T` are exactly the finite
`ℂ`-combinations of translations by members of `T`. -/
def AllSupportedHaveL2SpectralRadiusProperty {G : Type u} [Group G] (T : Set G) : Prop :=
  ∀ (m : ℕ) (c : Fin m → ℂ) (γ : Fin m → G), (∀ i, γ i ∈ T) →
    HasL2SpectralRadiusProperty (∑ i : Fin m, c i • reducedLeftRegular G (γ i))

/-! ## The two named inputs -/

/-- **Dykema--de la Harpe, Theorem 1.4**, which Gerasimova and Osin quote as
their Theorem 5.4:

> Suppose that for any finite subset `F` of a group `G`, there exists `t ∈ G`
> such that `tF` generates a free subsemigroup and every `a ∈ ℂG` with
> `supp(a) ⊆ tF` has the `ℓ²`-spectral radius property.  Then `sr(C*_r(G)) = 1`.

A theorem about reduced group C⋆-algebras; no hyperbolic geometry occurs in it. -/
def DykemaDeLaHarpeTheorem14 : Prop :=
  ∀ (G : Type) [Group G],
    (∀ F : Finset G, ∃ t : G,
      FreelyGeneratesFreeSubsemigroup ((fun x ↦ t * x) '' (F : Set G)) ∧
        AllSupportedHaveL2SpectralRadiusProperty ((fun x ↦ t * x) '' (F : Set G))) →
      IsStableRankOne (ReducedGroupCStar G)

/-- **Gerasimova--Osin's Propositions 4.1 and 2.4, combined into what their
Theorem 5.4 consumes.**

Proposition 4.1 produces the combing and the element `t`; Proposition 2.4 turns
the combing's linear growth into the norm comparison `‖a‖ ≤ γ(ρ(n))^{3/2}‖a‖₂`
on the free subsemigroup, and polynomial growth of `γ ∘ ρ` makes that comparison
give the `ℓ²`-spectral radius property.  This Prop is the whole geometric
content of their paper. -/
def GerasimovaOsinFreeSubsemigroupInput : Prop :=
  ∀ (G : Type) [Group G] [Countable G] [IsAcylindricallyHyperbolic G],
    HasTrivialFiniteRadical G →
      ∀ F : Finset G, ∃ t : G,
        FreelyGeneratesFreeSubsemigroup ((fun x ↦ t * x) '' (F : Set G)) ∧
          AllSupportedHaveL2SpectralRadiusProperty ((fun x ↦ t * x) '' (F : Set G))

/-! ## The assembly -/

/-- **`GerasimovaOsinTheorem11Printed` from the two named inputs.** -/
theorem gerasimovaOsinTheorem11Printed_of_inputs
    (hDH : DykemaDeLaHarpeTheorem14)
    (hGO : GerasimovaOsinFreeSubsemigroupInput) :
    GerasimovaOsinTheorem11Printed := by
  intro G instG instC instAH hrad
  letI := instG
  letI := instC
  letI := instAH
  exact hDH G (hGO G hrad)

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms reducedTwoNorm_le_norm
#audit_axioms reducedTwoNorm_pow_rpow_le
#audit_axioms gerasimovaOsinTheorem11Printed_of_inputs
