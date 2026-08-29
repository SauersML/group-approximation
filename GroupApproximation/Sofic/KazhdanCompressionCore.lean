import GroupApproximation.Kazhdan.Kazhdan

/-!
# Marker-free Kazhdan-compression data

This module records exactly the group-theoretic input used by the compressor
and finite-normal obstruction: a property-`(T)` source mapped into an ambient
group, a one-sided compressor of its image, and a root centralizing that
image.  It deliberately contains no marked element, torsion relation, or
central marked word.

The compression-defect subgroup is the normal closure of the pointwise
commutators `[t c t⁻¹, ι(γ)]`.  Its elementary normal-closure API is kept here
so the analytic files depend on a genuinely marker-free interface.
-/

namespace GroupApproximation

open scoped commutatorElement

universe u v

/-- The exact marker-free input to Kazhdan compression. -/
structure KazhdanCompressionCore (Γ : Type v) (E : Type u) [Group Γ]
    [Group E] where
  /-- The Kazhdan source mapped into the ambient group. -/
  iota : Γ →* E
  /-- The element compressing the image of `Γ`. -/
  t : E
  /-- The root element centralized by the Kazhdan image. -/
  c : E
  /-- Property `(T)` for the source. -/
  kazhdan : HasKazhdanPropertyT.{v, v} Γ
  /-- Conjugation by `t` carries `ι(Γ)` back into `ι(Γ)`. -/
  compresses : ∀ γ : Γ, ∃ δ : Γ, t * iota γ * t⁻¹ = iota δ
  /-- The root centralizes the image of `Γ`. -/
  comm_c : ∀ γ : Γ, Commute c (iota γ)

end GroupApproximation
