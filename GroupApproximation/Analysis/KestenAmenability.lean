import GroupApproximation.Analysis.LancePositiveDefinite
import GroupApproximation.Meta.AxiomGuard

/-!
# Kesten's criterion: a maximal translation sum forces an invariant mean

## The statement

For a discrete group `G` and a finite family `s : Fin n → G`, the operator
`∑ᵢ λ_{s i}` on `ℓ²(G)` has norm at most `n`, since it is a sum of `n`
unitaries.  **Kesten's criterion** is that equality for *every* family forces
amenability:

> if for every finite family and every tolerance there is a unit vector `ξ`
> with `‖∑ᵢ λ_{s i} ξ‖² ≥ n² − η`, then `G` carries a left-invariant mean.

`hasInvariantMean_of_translationSum_almost_maximal` is that implication,
proved.  It is stated on finitely supported vectors, which is the form
`Analysis/LancePositiveDefinite` develops and the form the Reiter assembly
consumes, so no Hilbert-space completion appears anywhere in the argument.

## Why the proof is three lines of geometry

Write `v i = λ_{s i} ξ`, a family of `n` unit vectors.  Then

  `‖∑ᵢ v i‖² = ∑ᵢⱼ re ⟪v i, v j⟫`

is a sum of `n²` terms, each at most `1` because `0 ≤ ‖v i − v j‖² = 2 − 2 re
⟪v i, v j⟫`.  A sum of `n²` terms each at most `1` that is at least `n² − η`
has *every* term at least `1 − η`.  Taking the family to begin with the
identity, the terms in the first row are exactly the matrix coefficients
`re ⟪ξ, λ_g ξ⟫`, so they are all within `η` of `1`, which is the hypothesis of
`hasInvariantMean_of_coefficients_near_one`.

No compactness, no ultrafilter and no functional calculus: the ultrafilter
limit is inside the Day/Reiter assembly this feeds, and the geometry above is
the whole of Kesten's step.

## What this is for

It is the second half of Lance's theorem stated at the tensor definition of
nuclearity, `‖·‖_min = ‖·‖_max`.  In that argument one shows that if the
minimal and maximal norms agree then `‖∑_{g ∈ F} λ_g‖ = |F|` for every finite
`F` — the maximal norm sees the trivial representation and the minimal norm
sees only the regular one — and this module turns that conclusion into
amenability.  The first half, the norm identification through Fell absorption,
is not here.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace LanceAmenability

universe u

variable {G : Type u} [Group G]

/-! ## Two unit vectors have real inner product at most one -/

omit [Group G] in
/-- **Cauchy--Schwarz in the only case needed**: the real part of the inner
product of two unit vectors is at most `1`, because the squared norm of their
difference is `2 − 2` times it. -/
theorem re_starInner_le_one {u v : G →₀ ℂ} (hu : l2NormSq u = 1)
    (hv : l2NormSq v = 1) : (starInner u v).re ≤ 1 := by
  have h := l2NormSq_sub v u
  rw [hu, hv] at h
  have hnn : 0 ≤ l2NormSq (v - u) := l2NormSq_nonneg _
  rw [h] at hnn
  linarith

/-! ## A sum of many terms, each at most one -/

omit [Group G] in
/-- If a sum over a finite index type of terms each at most `1` is at least
`(card) − η`, then every term is at least `1 − η`.  The other terms carry at
most `card − 1` between them. -/
theorem le_of_sum_le_card_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → ℝ) (hle : ∀ i, t i ≤ 1) {η : ℝ}
    (hsum : (Fintype.card ι : ℝ) - η ≤ ∑ i, t i) (i₀ : ι) :
    1 - η ≤ t i₀ := by
  classical
  have hsplit : ∑ i, t i
      = t i₀ + ∑ i ∈ Finset.univ.erase i₀, t i :=
    (Finset.add_sum_erase _ t (Finset.mem_univ i₀)).symm
  have hrest : ∑ i ∈ Finset.univ.erase i₀, t i
      ≤ ((Finset.univ.erase i₀).card : ℝ) := by
    calc ∑ i ∈ Finset.univ.erase i₀, t i
        ≤ ∑ _i ∈ Finset.univ.erase i₀, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ ↦ hle i
      _ = ((Finset.univ.erase i₀).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : ((Finset.univ.erase i₀).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀)]
    have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₀⟩
    push_cast [Finset.card_univ]
    rw [Nat.cast_sub hpos]
    norm_num
  rw [hsplit] at hsum
  rw [hcard] at hrest
  linarith

/-! ## The squared norm of a sum of translates -/

/-- The squared norm of a sum of translates is the sum of the real parts of
the pairwise inner products. -/
theorem l2NormSq_sum_lTrans {n : ℕ} (s : Fin n → G) (ξ : G →₀ ℂ) :
    l2NormSq (∑ i, lTrans (s i) ξ)
      = ∑ i, ∑ j, (starInner (lTrans (s i) ξ) (lTrans (s j) ξ)).re := by
  have hself := starInner_self (∑ i, lTrans (s i) ξ)
  have hexp : starInner (∑ i, lTrans (s i) ξ) (∑ j, lTrans (s j) ξ)
      = ∑ i, ∑ j, starInner (lTrans (s i) ξ) (lTrans (s j) ξ) := by
    rw [starInner_finsetSum_left]
    exact Finset.sum_congr rfl fun i _ ↦ starInner_finsetSum_right _ _
  rw [hexp] at hself
  have hre := congrArg Complex.re hself
  rw [Complex.ofReal_re] at hre
  rw [← hre]
  simp only [Complex.re_sum]

/-! ## Kesten's criterion -/

/-- **Kesten's criterion.**  If for every finite family of group elements and
every tolerance there is a unit vector whose translates almost add up to their
number, then the group carries a left-invariant mean.

The hypothesis is the `ℓ²`-vector form of `‖∑ᵢ λ_{s i}‖ = n`, which is the
largest value a sum of `n` unitaries can have. -/
theorem hasInvariantMean_of_translationSum_almost_maximal
    (h : ∀ (n : ℕ) (s : Fin n → G) (η : ℝ), 0 < η →
      ∃ ξ : G →₀ ℂ, l2NormSq ξ = 1 ∧
        (n : ℝ) ^ 2 - η ≤ l2NormSq (∑ i, lTrans (s i) ξ)) :
    Amenability.HasInvariantMean G := by
  classical
  refine hasInvariantMean_of_coefficients_near_one fun F ε hε ↦ ?_
  -- enumerate `F` after the identity
  set m := F.card with hm
  set e : Fin m ≃ {x // x ∈ F} := (F.equivFin).symm with he
  set s : Fin (m + 1) → G := Fin.cons (1 : G) (fun i ↦ ((e i : {x // x ∈ F}) : G))
    with hs
  obtain ⟨ξ, hξ, hbig⟩ := h (m + 1) s ε hε
  -- every pairwise inner product is at most one
  have hunit : ∀ i : Fin (m + 1), l2NormSq (lTrans (s i) ξ) = 1 := by
    intro i
    rw [l2NormSq_lTrans, hξ]
  have hle : ∀ p : Fin (m + 1) × Fin (m + 1),
      (starInner (lTrans (s p.1) ξ) (lTrans (s p.2) ξ)).re ≤ 1 := by
    rintro ⟨i, j⟩
    exact re_starInner_le_one (hunit i) (hunit j)
  -- the double sum, as a sum over pairs
  have hsum : ((Fintype.card (Fin (m + 1) × Fin (m + 1)) : ℝ)) - ε
      ≤ ∑ p : Fin (m + 1) × Fin (m + 1),
          (starInner (lTrans (s p.1) ξ) (lTrans (s p.2) ξ)).re := by
    have hprod : (∑ p : Fin (m + 1) × Fin (m + 1),
        (starInner (lTrans (s p.1) ξ) (lTrans (s p.2) ξ)).re)
        = ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            (starInner (lTrans (s i) ξ) (lTrans (s j) ξ)).re := by
      rw [Fintype.sum_prod_type]
    have hcard : (Fintype.card (Fin (m + 1) × Fin (m + 1)) : ℝ)
        = (((m + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [Fintype.card_prod, Fintype.card_fin]
      push_cast
      ring
    rw [hcard, hprod, ← l2NormSq_sum_lTrans s ξ]
    exact hbig
  -- read off the first row
  refine ⟨ξ, hξ, fun g hg ↦ ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : Fin m, ((e k : {x // x ∈ F}) : G) = g := by
    refine ⟨F.equivFin ⟨g, hg⟩, ?_⟩
    rw [he]
    simp
  have hterm : 1 - ε ≤ (starInner (lTrans (s 0) ξ) (lTrans (s k.succ) ξ)).re :=
    le_of_sum_le_card_sub _ hle hsum (0, k.succ)
  have hval : (starInner (lTrans (s 0) ξ) (lTrans (s k.succ) ξ)).re
      = (coeffFn ξ g).re := by
    have h0 : s 0 = (1 : G) := by rw [hs]; simp
    have hk' : s k.succ = g := by rw [hs]; simpa using hk
    rw [h0, hk', lTrans_one]
    rfl
  rw [hval] at hterm
  exact hterm

end LanceAmenability
end GroupApproximation

open GroupApproximation.LanceAmenability

#audit_axioms
  GroupApproximation.LanceAmenability.hasInvariantMean_of_translationSum_almost_maximal
