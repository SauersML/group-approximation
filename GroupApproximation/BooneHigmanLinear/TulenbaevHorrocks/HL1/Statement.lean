import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HL1.RelMap
import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HL1.Laurent
import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Field

/-!
# H.L1: `St_N(B) → St_N(A[X, X⁻¹])` is injective (Tulenbaev, Corollary 4.2)

Let `A` be a local ring with maximal ideal `𝔪`, `R = A[T, T⁻¹]` and
`B = A[T⁻¹] + 𝔪[T] ⊆ R` (pal-q111's `Graded.horrB 𝔪`). Tulenbaev's Corollary 4.2 says that
`St_N(B) → St_N(R)` is injective (`StHorrBInjAt`, the form H.L5 consumes).

Tulenbaev's proof has three inputs:
* `KerStepAt`: an element of `St_N(B)` that dies in `St_N(R)` comes from the relative group
  `St_N(B, 𝔪R ∩ B)`. This is the field case (`St_N(k[T⁻¹]) → St_N(k[T, T⁻¹])` injective, Quillen
  and K₂-stability) plus the normal generation of `ker(St_N(B) → St_N(k[T⁻¹]))`.
* `DilationAt` (T Lemma 3.2): a homomorphism `D : St_N(R, 𝔪R) → St_N(B)` extending the canonical
  map of the relative group of `B`, and killing the relative elements of `A[T⁻¹]` that die in
  `St_N(A[T⁻¹])`.
* `KerLiftAt` (T Prop 4.1, with `X ↦ X⁻¹`): an element of `St_N(R, 𝔪R)` that dies in `St_N(R)`
  comes from `St_N(A[T⁻¹], 𝔪[T⁻¹])`, from an element that dies in `St_N(A[T⁻¹])`.

`stHorrBInjAt_of_steps` assembles them, given van der Kallen's elements over `B` and `R` that are
natural along `B ⊆ R` (`VdKNatural` provides these for `4 ≤ N`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks
namespace HL1

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Found
open GroupApproximation.BooneHigmanLinear.K2Found.RelPres (RelSt can)
open GroupApproximation.BooneHigmanLinear.Tulenbaev (toLaurentNeg)

section Defs

variable (A : Type) [CommRing A] [IsLocalRing A]

/-- `B = A[T⁻¹] + 𝔪[T]`. -/
abbrev horrBm : Subring (LaurentPolynomial A) :=
  Graded.horrB (IsLocalRing.maximalIdeal A)

/-- **H.L1 (Tulenbaev, Cor 4.2).** `St_N(A[T⁻¹] + 𝔪[T]) → St_N(A[T, T⁻¹])` is injective. -/
def StHorrBInjAt (N : ℕ) : Prop :=
  Function.Injective (ringMap (I := Fin N) (horrBm A).subtype)

#audit_axioms StHorrBInjAt

/-- `𝔪R ⊆ R = A[T, T⁻¹]`: the Laurent polynomials with coefficients in `𝔪`. -/
abbrev mR : Ideal (LaurentPolynomial A) :=
  coeffIdeal (IsLocalRing.maximalIdeal A)

/-- `𝔪R ∩ B`. -/
abbrev mB : Ideal (horrBm A) :=
  Ideal.comap (horrBm A).subtype (mR A)

/-- `𝔪[T] ⊆ A[T]`; under `T ↦ T⁻¹` it is Tulenbaev's `𝔪[X⁻¹]`. -/
abbrev mP : Ideal (Polynomial A) :=
  Ideal.map (Polynomial.C : A →+* Polynomial A) (IsLocalRing.maximalIdeal A)

theorem mB_le : mB A ≤ (mR A).comap (horrBm A).subtype :=
  le_rfl

theorem mP_le : mP A ≤ (mR A).comap (toLaurentNeg A) := by
  refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
  have e := RingHom.congr_fun (toLaurentNeg_comp_C (A := A)) a
  rw [RingHom.comp_apply] at e
  show toLaurentNeg A (Polynomial.C a) ∈ mR A
  rw [e]
  exact C_mem_coeffIdeal ha

variable (N : ℕ)

/-- **The kernel step** (field case plus normal generation): an element of `St_N(B)` that dies in
`St_N(R)` comes from `St_N(B, 𝔪R ∩ B)`. -/
def KerStepAt (hB : VdK.Elements (Fin N) (horrBm A)) : Prop :=
  ∀ α : SteinbergGroup (Fin N) (horrBm A), ringMap (horrBm A).subtype α = 1 →
    α ∈ (can hB (mB A)).range

/-- **Tulenbaev, Lemma 3.2** (dilation). -/
def DilationAt (hB : VdK.Elements (Fin N) (horrBm A))
    (hP : VdK.Elements (Fin N) (Polynomial A)) : Prop :=
  ∃ D : RelSt (Fin N) (LaurentPolynomial A) (mR A) →* SteinbergGroup (Fin N) (horrBm A),
    D.comp (relMap (horrBm A).subtype (mB_le A)) = can hB (mB A) ∧
      ∀ γ : RelSt (Fin N) (Polynomial A) (mP A), can hP (mP A) γ = 1 →
        D (relMap (toLaurentNeg A) (mP_le A) γ) = 1

/-- **Tulenbaev, Proposition 4.1** (with `X ↦ X⁻¹`). -/
def KerLiftAt (hR : VdK.Elements (Fin N) (LaurentPolynomial A))
    (hP : VdK.Elements (Fin N) (Polynomial A)) : Prop :=
  ∀ β : RelSt (Fin N) (LaurentPolynomial A) (mR A), can hR (mR A) β = 1 →
    ∃ γ : RelSt (Fin N) (Polynomial A) (mP A), can hP (mP A) γ = 1 ∧
      relMap (toLaurentNeg A) (mP_le A) γ = β

end Defs

/-- **Tulenbaev, Corollary 4.2, from its three steps.** -/
theorem stHorrBInjAt_of_steps (A : Type) [CommRing A] [IsLocalRing A] (N : ℕ)
    (hB : VdK.Elements (Fin N) (horrBm A)) (hR : VdK.Elements (Fin N) (LaurentPolynomial A))
    (hP : VdK.Elements (Fin N) (Polynomial A))
    (hnat : ∀ (p : (Fin N → horrBm A) × (Fin N → horrBm A)) (hp : p ∈ VdK.U (Fin N) (horrBm A))
      (hp' : mapPair (horrBm A).subtype p ∈ VdK.U (Fin N) (LaurentPolynomial A)),
      ringMap (horrBm A).subtype (hB.elt p hp) = hR.elt (mapPair (horrBm A).subtype p) hp')
    (hK : KerStepAt A N hB) (hD : DilationAt A N hB hP) (hL : KerLiftAt A N hR hP) :
    StHorrBInjAt A N := by
  have hcan := can_relMap hB hR (horrBm A).subtype (mB_le A) hnat
  obtain ⟨D, hD1, hD2⟩ := hD
  rw [StHorrBInjAt, injective_iff_map_eq_one]
  intro α hα
  obtain ⟨β₀, rfl⟩ := MonoidHom.mem_range.1 (hK α hα)
  have hβ : can hR (mR A) (relMap (horrBm A).subtype (mB_le A) β₀) = 1 := by
    have h := DFunLike.congr_fun hcan β₀
    simp only [MonoidHom.comp_apply] at h
    rw [h]
    exact hα
  obtain ⟨γ, hγ1, hγ2⟩ := hL _ hβ
  have h := DFunLike.congr_fun hD1 β₀
  simp only [MonoidHom.comp_apply] at h
  rw [← h, ← hγ2]
  exact hD2 γ hγ1

#audit_axioms stHorrBInjAt_of_steps

end HL1
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
