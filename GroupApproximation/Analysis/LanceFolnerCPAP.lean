import GroupApproximation.Analysis.LanceFolnerMaps
import GroupApproximation.Analysis.LanceNuclearity

/-!
# The Følner factorization: what the two maps do to a translation

`Analysis/LanceFolnerMaps` builds the compression `J⋆ · J` to `k`
coordinates and the Choi-type map back, and proves each of them completely
positive.  This file computes the **composite**, which is the entire content
of Lance's forward direction:

  `up (down λ_g) = ω_g · λ_g`,

a scalar multiple of the same translation, the scalar being the *overlap*

  `ω_g = ∑_{p,q} [e p = g · e q] · c̄_p c_q`.

Everything else is arithmetic.  `nuclearReducedCPAP_of_overlap` packages it:
if for every finite set of translations and every tolerance there is a tuple
`(e, c)` --- injective enumeration, unit amplitudes --- whose overlaps are
within the tolerance of `1`, then `C⋆_λ(G)` has the completely positive
approximation property in the repository's sense
(`CStarExactness.NuclearReducedCPAP`).

Contractivity is not proved by hand anywhere: both maps are unital and
completely positive, so `IsCompletelyPositive.norm_apply_le_of_unital`
applies.  Unitality of the compression is injectivity of `e`; unitality of
the Følner map is `∑_p |c_p|² = 1`.

The remaining input --- that an amenable group supplies such tuples --- is
`Analysis/LanceAmenableOverlap`; it is Finset counting over the Følner sets
that `Sofic/AmenableActionSofic.exists_folner` already produces.

## Manuscript status

Infrastructure for the Lance lane; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open Finset ReducedGroupCStarTrace GroupVonNeumann

noncomputable section

universe u

variable {G : Type u} [Group G]

/-! ## Translations move point masses -/

/-- The left regular representation permutes the point masses. -/
theorem leftRegularOperator_single (g t : G) :
    leftRegularOperator G g (lp.single 2 t (1 : ℂ) : GroupHilbert G)
      = (lp.single 2 (g * t) (1 : ℂ) : GroupHilbert G) := by
  classical
  apply lp.ext
  funext x
  rw [leftRegularOperator_apply]
  by_cases h : x = g * t
  · subst h
    rw [inv_mul_cancel_left, lp.single_apply_self, lp.single_apply_self]
  · have h' : g⁻¹ * x ≠ t := fun hc ↦ h (inv_mul_eq_iff_eq_mul.mp hc)
    rw [lp.single_apply_ne _ _ _ h', lp.single_apply_ne _ _ _ h]

/-- The inclusion sends the standard basis to the prescribed point masses. -/
theorem folnerIncl_single {k : ℕ} (e : Fin k → G) (q : Fin k) :
    folnerIncl e (EuclideanSpace.single q (1 : ℂ))
      = (lp.single 2 (e q) (1 : ℂ) : GroupHilbert G) := by
  classical
  rw [folnerIncl_apply, Finset.sum_eq_single q]
  · rw [PiLp.single_apply, if_pos rfl, one_smul]
  · intro i _ hi
    rw [PiLp.single_apply, if_neg hi, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ q) h

/-- The matrix entries of a compressed translation are the incidence
coefficients of the enumeration. -/
theorem euclideanEntry_compression_leftRegular {k : ℕ} (e : Fin k → G)
    (g : G) (p q : Fin k) :
    euclideanEntryLM k p q
        (compressionLM (folnerIncl e) (leftRegularOperator G g))
      = if e p = g * e q then 1 else 0 := by
  classical
  rw [euclideanEntry_compressionLM, folnerIncl_single, folnerIncl_single,
    leftRegularOperator_single, inner_single_single]

/-! ## The overlap -/

/-- The **Følner overlap** of `g`: the scalar by which the factorization
multiplies `λ_g`. -/
def folnerOverlap {k : ℕ} (e : Fin k → G) (c : Fin k → ℂ) (g : G) : ℂ :=
  ∑ p : Fin k, ∑ q : Fin k, if e p = g * e q then star (c p) * c q else 0

/-- **The composite is a scalar multiple of the same translation.** -/
theorem folnerUp_compression_leftRegular {k : ℕ} (e : Fin k → G)
    (c : Fin k → ℂ) (g : G) :
    folnerUp e c (compressionLM (folnerIncl e) (leftRegularOperator G g))
      = folnerOverlap e c g • leftRegularOperator G g := by
  classical
  rw [folnerUp_apply, folnerOverlap, Finset.sum_smul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [euclideanEntry_compression_leftRegular,
    star_folnerTuple_mul_folnerTuple]
  by_cases h : e p = g * e q
  · have hg : e p * (e q)⁻¹ = g := by rw [h, mul_inv_cancel_right]
    rw [if_pos h, if_pos h, one_smul, hg]
  · rw [if_neg h, if_neg h, zero_smul, zero_smul]

/-! ## Unitality -/

/-- The matrix entries of the identity. -/
theorem euclideanEntry_one {k : ℕ} (p q : Fin k) :
    euclideanEntryLM k p q
        (1 : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k))
      = if p = q then 1 else 0 := by
  classical
  rw [euclideanEntryLM_apply]
  show ⟪(EuclideanSpace.single p (1 : ℂ) : EuclideanSpace ℂ (Fin k)),
    (EuclideanSpace.single q (1 : ℂ) : EuclideanSpace ℂ (Fin k))⟫_ℂ = _
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.single_apply]
  by_cases h : p = q
  · simp [h]
  · simp [h, Ne.symm h]

/-- **The Følner map is unital** exactly when the amplitudes are a unit
vector. -/
theorem folnerUp_one {k : ℕ} (e : Fin k → G) (c : Fin k → ℂ)
    (hc : (∑ p : Fin k, star (c p) * c p) = 1) :
    folnerUp e c 1 = 1 := by
  classical
  rw [folnerUp_apply]
  have hterm : ∀ p : Fin k,
      (∑ q : Fin k, euclideanEntryLM k p q
          (1 : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k))
        • (star (folnerTuple e c p) * folnerTuple e c q))
      = (star (c p) * c p) • (1 : GroupHilbert G →L[ℂ] GroupHilbert G) := by
    intro p
    rw [Finset.sum_eq_single p]
    · rw [euclideanEntry_one, if_pos rfl, one_smul,
        star_folnerTuple_mul_folnerTuple, mul_inv_cancel,
        leftRegularOperator_one]
    · intro q _ hq
      rw [euclideanEntry_one, if_neg (Ne.symm hq), zero_smul]
    · intro h
      exact absurd (Finset.mem_univ p) h
  rw [Finset.sum_congr rfl fun p _ ↦ hterm p, ← Finset.sum_smul, hc, one_smul]

/-! ## The completely positive approximation property -/

/-- **The forward half of Lance's theorem, at the interface.**  A group
whose translations admit enumerations with almost-unit overlaps has a
reduced C⋆-algebra with the completely positive approximation property. -/
theorem nuclearReducedCPAP_of_overlap {Γ : Type} [Group Γ]
    (h : ∀ (F : Finset Γ) (δ : ℝ), 0 < δ →
      ∃ (k : ℕ) (e : Fin k → Γ) (c : Fin k → ℂ),
        Function.Injective e ∧ (∑ p : Fin k, star (c p) * c p) = 1 ∧
          ∀ g ∈ F, ‖folnerOverlap e c g - 1‖ ≤ δ) :
    NuclearReducedCPAP Γ := by
  classical
  intro F ε hε
  obtain ⟨k, e, c, he, hc, hoverlap⟩ := h F ε hε
  set incl : ↥(reducedGroupCStarSubalgebra Γ) →⋆ₙₐ[ℂ]
      (GroupHilbert Γ →L[ℂ] GroupHilbert Γ) :=
    (reducedGroupCStarSubalgebra Γ).subtype.toNonUnitalStarAlgHom with hincl
  set down : ↥(reducedGroupCStarSubalgebra Γ) →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) :=
    (compressionLM (folnerIncl e)).comp
      ((incl : ↥(reducedGroupCStarSubalgebra Γ) →ₗ[ℂ]
        (GroupHilbert Γ →L[ℂ] GroupHilbert Γ))) with hdown
  have hdowncp : IsCompletelyPositive down :=
    (isCompletelyPositive_compressionLM (folnerIncl e)).comp
      (isCompletelyPositive_of_starAlgHom incl)
  have hdownapp : ∀ b : ↥(reducedGroupCStarSubalgebra Γ),
      down b = compressionLM (folnerIncl e)
        (b : GroupHilbert Γ →L[ℂ] GroupHilbert Γ) := fun _ ↦ rfl
  refine ⟨k, down, folnerUp e c, ?_, ?_, ?_,
    isCompletelyPositive_folnerUp e c, folnerUp_one e c hc,
    folnerUp_mem_reduced e c, ?_⟩
  · intro m a v
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · haveI : NeZero m := ⟨by omega⟩
      exact (hdowncp.form_nonneg a v).1
  · intro b
    rw [hdownapp, hdownapp]
    show compressionLM (folnerIncl e)
        (star (b : GroupHilbert Γ →L[ℂ] GroupHilbert Γ))
      = star (compressionLM (folnerIncl e)
        (b : GroupHilbert Γ →L[ℂ] GroupHilbert Γ))
    exact compressionLM_star _ _
  · rw [hdownapp]
    show compressionLM (folnerIncl e)
      (1 : GroupHilbert Γ →L[ℂ] GroupHilbert Γ) = 1
    exact compressionLM_one he
  · intro g hg
    rw [hdownapp]
    show ‖folnerUp e c
        (compressionLM (folnerIncl e) (leftRegularOperator Γ g))
      - leftRegularOperator Γ g‖ ≤ ε
    rw [folnerUp_compression_leftRegular, ← sub_smul]
    refine le_trans (norm_smul_le _ _) ?_
    calc ‖folnerOverlap e c g - 1‖ * ‖leftRegularOperator Γ g‖
        ≤ ε * 1 :=
          mul_le_mul (hoverlap g hg) (norm_leftRegularOperator_le_one Γ g)
            (norm_nonneg _) (le_of_lt hε)
      _ = ε := mul_one ε

end

end CStarExactness
end GroupApproximation
