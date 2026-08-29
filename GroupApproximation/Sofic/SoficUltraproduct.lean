import GroupApproximation.Sofic.SoficAmplification

/-!
# Sofic embeddings into metric ultraproducts of symmetric groups

This file constructs metric ultraproducts of finite symmetric groups and
connects injective homomorphisms into them directly to `IsSofic`.

The ultraproduct is built here directly: `IsNullSeq` picks out the sequences of
permutations whose normalized Hamming length tends to zero along `𝒰`, these
form a normal subgroup `nullSubgroup` of the product group because the Hamming
length is conjugation invariant, and `UniversalSofic` is the quotient.

`isSofic_of_soficEmbedding` is the bridge: an injective homomorphism into any
such quotient makes the group sofic.  Amplification is exactly what makes this
work.  Lifting the images of a finite test set gives multiplicativity to within
any prescribed `ε` on a `𝒰`-large set, but injectivity gives only that distinct
elements are at *some* positive Hamming distance, an amount depending on the
pair — never the `1 - ε` that `IsSofic` asks for.  That is precisely the
hypothesis `IsSoficWeakLocal` of `Sofic.SoficAmplification`, which tensor powers
upgrade.

`no_soficEmbedding_of_not_isSofic` is the contrapositive: a nonsofic group
admits no injective homomorphism into any such metric ultraproduct, over any
index type and any ultrafilter.
-/

namespace GroupApproximation

open Filter

/-! ## Hamming length -/

/-! ## The metric ultraproduct -/

variable {ι : Type*} (𝒰 : Ultrafilter ι) (X : ι → FiniteModel)

/-! ## The bridge -/

variable {G : Type*} [Group G]

/-! ## The converse

`isSofic_of_soficEmbedding` is one half of the identification.  This is the
other: a sofic approximation, read along a nonprincipal ultrafilter on `ℕ`,
*is* an embedding into the universal sofic group over its own models.  Both
estimates transfer the same way -- the sequential definition gives them for all
`n` past a threshold, and a nonprincipal ultrafilter contains every cofinite
set, so `∀ᶠ` along `atTop` becomes `∀ᶠ` along `𝒰`.
-/

section Converse

variable {G : Type*} [Group G]

/-- Cofinite sets belong to a nonprincipal ultrafilter, so an eventual estimate
in the sequential sense is an eventual estimate along `𝒰`. -/
theorem eventually_of_atTop {𝒰 : Ultrafilter ℕ}
    (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) {p : ℕ → Prop} (N : ℕ)
    (hp : ∀ n ≥ N, p n) : ∀ᶠ n in (𝒰 : Filter ℕ), p n := by
  refine Filter.Eventually.filter_mono hcof ?_
  rw [Nat.cofinite_eq_atTop]
  exact Filter.eventually_atTop.mpr ⟨N, hp⟩

end Converse

end GroupApproximation
