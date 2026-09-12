import GroupApproximation.Sofic.HilbertUltraproductInner

/-!
# `K_ω` as an inner-product space

`Sofic/HilbertUltraproductInner.lean` puts the manuscript's form
`⟨ξ, η⟩ = lim_ω Tr(ξ_n* η_n)/w_n` on the numerator of `Vec`.  This file descends
it to `Vec` itself and records the four properties that make the descended form
an inner product: conjugate symmetry, positivity, additivity and homogeneity,
and — the one with content — **definiteness**, which holds precisely because the
denominator of `Vec` is the set of families null at the weight, i.e. exactly the
null space of the form.

That last equivalence,

  `⟨[ξ], [ξ]⟩ = 0  ↔  ξ is null at the weight along ω`,

is what makes `Vec` the *Hilbert-space* ultraproduct rather than merely its
underlying module, and it is the step `UltraproductModelConstruction` deferred
when it wrote that the inner product is "deliberately not built".
-/

namespace GroupApproximation
namespace HilbertUltraproductSpace

open Filter Matrix Topology
open UltrafilterLimit UltraproductModelConstruction
open HilbertUltraproductInner HilbertUltraproductPairing ScaledKazhdanTransport

noncomputable section

variable {Y : ℕ → FiniteModel} {w : ℕ → ℝ} {ω : Ultrafilter ℕ}

/-! ## Null families are exactly the isotropic ones -/

/-- A family null at the weight has vanishing self-pairing. -/
theorem uinner_self_eq_zero_of_massNull (hw : ∀ n, 0 ≤ w n)
    {ξ : massBounded Y w} (hξ : (ξ : MatFam Y) ∈ massNull Y w ω) :
    uinner (ω := ω) ξ ξ = 0 :=
  uinner_eq_zero_of_massNull_left hw hξ

/-- **Definiteness.**  Conversely, a mass-bounded family whose self-pairing
vanishes is null at the weight: the limit of the renormalized masses is zero,
so each `ε` bounds them on a set of `ω`, and at the stages where the weight
vanishes the family does too. -/
theorem massNull_of_uinner_self_eq_zero (hw : ∀ n, 0 ≤ w n)
    {ξ : massBounded Y w} (h : uinner (ω := ω) ξ ξ = 0) :
    (ξ : MatFam Y) ∈ massNull Y w ω := by
  obtain ⟨Cx, hx⟩ := ξ.2
  have hmass : ulim ω (fun n ↦ matMass ((ξ : MatFam Y) n) / w n) = 0 := by
    have := uinner_self hw ξ (ω := ω)
    rw [h] at this
    exact_mod_cast this.symm
  intro ε hε
  have hlt := eventually_lt_of_ulim_eq_zero (exists_tendsto_mass hw ξ) hmass hε
  filter_upwards [hlt] with n hn
  have hclip : clipWeight w n = w n := max_eq_left (hw n)
  rw [hclip]
  rcases (hw n).lt_or_eq with hpos | hzero
  · exact le_of_lt ((div_lt_iff₀ hpos).mp hn)
  · have hxn : (ξ : MatFam Y) n = 0 := eq_zero_of_weight_eq_zero hx hzero.symm
    rw [hxn, matMass_zero, ← hzero]
    simp

/-- The two together: the form's null vectors are exactly the denominator of
`Vec`. -/
theorem uinner_self_eq_zero_iff (hw : ∀ n, 0 ≤ w n) (ξ : massBounded Y w) :
    uinner (ω := ω) ξ ξ = 0 ↔ (ξ : MatFam Y) ∈ massNull Y w ω :=
  ⟨fun h ↦ massNull_of_uinner_self_eq_zero hw h,
   fun h ↦ uinner_self_eq_zero_of_massNull hw h⟩

/-! ## Descent to the quotient -/

/-- Vanishing in the second argument against a null family, by conjugate
symmetry. -/
theorem uinner_eq_zero_of_massNull_right (hw : ∀ n, 0 ≤ w n)
    {ξ ζ : massBounded Y w} (hζ : (ζ : MatFam Y) ∈ massNull Y w ω) :
    uinner (ω := ω) ξ ζ = 0 := by
  have h := uinner_eq_zero_of_massNull_left hw (η := ξ) hζ
  have hconj := uinner_conj_symm hw ξ ζ (ω := ω)
  rw [h, map_zero] at hconj
  exact hconj.symm

/-- Additivity in the first argument, from conjugate symmetry. -/
theorem uinner_add_left (hw : ∀ n, 0 ≤ w n) (ξ η ζ : massBounded Y w) :
    uinner (ω := ω) (ξ + η) ζ = uinner (ω := ω) ξ ζ + uinner (ω := ω) η ζ := by
  have key : (starRingEnd ℂ) (uinner (ω := ω) (ξ + η) ζ)
      = (starRingEnd ℂ) (uinner (ω := ω) ξ ζ + uinner (ω := ω) η ζ) := by
    rw [map_add, uinner_conj_symm hw ζ (ξ + η), uinner_conj_symm hw ζ ξ,
      uinner_conj_symm hw ζ η]
    exact uinner_add_right hw ζ ξ η
  exact star_injective key

end

end HilbertUltraproductSpace
end GroupApproximation
