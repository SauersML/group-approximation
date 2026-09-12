import GroupApproximation.Manuscript.NonMF.GerasimovaOsinFreeSemigroupNorm
import GroupApproximation.Manuscript.NonMF.GerasimovaOsinSpectralRadius
import GroupApproximation.Analysis.GelfandSpectralRadiusLimsup
import GroupApproximation.Analysis.RordamDistanceOne
import GroupApproximation.Analysis.ReducedGroupCStarSpan

/-!
# Dykema–de la Harpe, Theorem 1.4, proved

> **Theorem 5.4** ([DH, Theorem 1.4], as quoted by Gerasimova–Osin).  Suppose that for
> any finite subset `F` of a group `G`, there exists `t ∈ G` such that `tF` generates a
> free subsemigroup and every `a ∈ ℂG` with `supp(a) ⊆ tF` has the `ℓ²`-spectral radius
> property.  Then `sr(C*_r(G)) = 1`.

`dykemaDeLaHarpeTheorem14 : DykemaDeLaHarpeTheorem14`, along the argument of
Dykema–Haagerup–Rørdam (Duke Math. J. 90 (1997), proof of Theorem 1.1 and the end of the
proof of Theorem 3.8):

1. For `y ∈ ℂG` with support `F`, take `t` from the hypothesis and `z = λ(t)·y`,
   supported in `tF`.  Then
   `dist(y, GL) = dist(z, GL) ≤ r(z) = r₂(z) = ‖z‖₂ = ‖y‖₂`: left multiplication by a
   unitary preserves the distance (DHR (3.3)), the distance is at most the spectral
   radius, the spectral radius property is the hypothesis, `r₂ = ‖·‖₂` on a free
   subsemigroup (`GerasimovaOsinFreeSemigroupNorm`), and `λ(t)` is an `ℓ²`-isometry
   (`distGL_le_reducedTwoNorm_finSum`).
2. Both sides are continuous and `ℂG` is dense, so `dist(x, GL) ≤ ‖x‖₂` for every
   `x ∈ C*_r(G)` (`distGL_le_reducedTwoNorm`).
3. If the invertibles were not dense, Rørdam's theorem (`Analysis/RordamDistanceOne`)
   gives `b` with `1 = ‖b‖ = dist(b, GL) ≤ ‖b‖₂ ≤ ‖b‖`.  Then `τ(1 − b^*b) = 0` and
   `τ(1 − bb^*) = 0` for the canonical faithful trace, with both elements positive, so
   `b` is unitary (`mem_unitary_of_norm_le_one_of_one_le_reducedTwoNorm`): at distance
   `0` from `GL`, a contradiction.

## Manuscript status

Discharges the analytic half of `cor:regular-nonmf-algebra`'s citation "Gerasimova and
Osin give density of the invertible elements, which is stable rank one".  The geometric
half is `GerasimovaOsinFreeSubsemigroupInput`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.ReducedGroupCStarTrace
open GroupApproximation.DistanceToInvertibles
open Filter
open scoped ComplexOrder

universe u

variable {G : Type u} [Group G]

/-- **Step 1: `dist(y, GL) ≤ ‖y‖₂` for `y ∈ ℂG`.** -/
theorem distGL_le_reducedTwoNorm_finSum
    (hDH : ∀ F : Finset G, ∃ t : G,
      FreelyGeneratesFreeSubsemigroup ((fun x ↦ t * x) '' (F : Set G)) ∧
        AllSupportedHaveL2SpectralRadiusProperty ((fun x ↦ t * x) '' (F : Set G)))
    {m : ℕ} (c : Fin m → ℂ) (γ : Fin m → G) :
    distGL (∑ i : Fin m, c i • reducedLeftRegular G (γ i))
      ≤ reducedTwoNorm (∑ i : Fin m, c i • reducedLeftRegular G (γ i)) := by
  classical
  rw [finSum_eq_translationSum]
  obtain ⟨t, hfree, hsrp⟩ := hDH (Finset.univ.image γ)
  have hTcoe : ((Finset.univ.image γ).image fun g => t * g : Finset G)
      = (fun x ↦ t * x) '' ((Finset.univ.image γ : Finset G) : Set G) := by
    rw [Finset.coe_image]
  have hz := leftRegular_mul_translationSum t (Finset.univ.image γ)
    (fun g => ∑ i ∈ Finset.univ.filter (fun i => γ i = g), c i)
  set T : Finset G := (Finset.univ.image γ).image fun g => t * g with hT
  set d : G → ℂ := fun h => ∑ i ∈ Finset.univ.filter (fun i => γ i = t⁻¹ * h), c i with hd
  have hsrpT : HasL2SpectralRadiusProperty (translationSum T d) := by
    have h := hsrp T.card (fun j => d (T.equivFin.symm j)) (fun j => (T.equivFin.symm j : G))
      (fun j => by
        rw [← hTcoe]
        exact Finset.mem_coe.mpr (T.equivFin.symm j).2)
    have heq : ∑ j : Fin T.card,
        d (T.equivFin.symm j) • reducedLeftRegular G (T.equivFin.symm j : G)
          = translationSum T d := by
      rw [translationSum, ← Finset.sum_coe_sort T]
      exact Equiv.sum_comp T.equivFin.symm (fun h : T => d h • reducedLeftRegular G (h : G))
    rwa [heq] at h
  have hfreeT : FreelyGeneratesFreeSubsemigroup (T : Set G) := by
    rw [hTcoe]
    exact hfree
  have hunit : reducedLeftRegular G t ∈ unitary (ReducedGroupCStar G) :=
    (reducedLeftRegularUnitary G t).2
  calc distGL (translationSum (Finset.univ.image γ)
        (fun g => ∑ i ∈ Finset.univ.filter (fun i => γ i = g), c i))
      = distGL (translationSum T d) := by rw [← hz, distGL_mul_of_mem_unitary hunit]
    _ ≤ (spectralRadius ℂ (translationSum T d)).toReal := distGL_le_spectralRadius _
    _ = operatorSpectralRadius (translationSum T d) :=
        (limsup_norm_pow_rpow_inv_eq_spectralRadius _).symm
    _ = l2SpectralRadius (translationSum T d) := hsrpT.symm
    _ = reducedTwoNorm (translationSum T d) :=
        l2SpectralRadius_translationSum_of_free T d hfreeT
    _ = reducedTwoNorm (translationSum (Finset.univ.image γ)
          (fun g => ∑ i ∈ Finset.univ.filter (fun i => γ i = g), c i)) := by
        rw [← hz, reducedTwoNorm_leftRegular_mul]

/-- The `ℓ²`-norm is `1`-Lipschitz for the operator norm. -/
theorem reducedTwoNorm_le_add_norm_sub (x y : ReducedGroupCStar G) :
    reducedTwoNorm x ≤ reducedTwoNorm y + ‖x - y‖ := by
  have h1 : reducedTwoNorm x ≤ reducedTwoNorm y + reducedTwoNorm (x - y) := by
    rw [reducedTwoNorm, reducedTwoNorm, reducedTwoNorm, AddSubgroupClass.coe_sub,
      sub_apply]
    calc ‖(x : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)‖
        = ‖(y : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)
            + ((x : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)
              - (y : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G))‖ := by
          congr 1
          abel
      _ ≤ _ := norm_add_le _ _
  linarith [reducedTwoNorm_le_norm (x - y)]

/-- **Step 2: `dist(x, GL) ≤ ‖x‖₂` on all of `C*_r(G)`.** -/
theorem distGL_le_reducedTwoNorm
    (hDH : ∀ F : Finset G, ∃ t : G,
      FreelyGeneratesFreeSubsemigroup ((fun x ↦ t * x) '' (F : Set G)) ∧
        AllSupportedHaveL2SpectralRadiusProperty ((fun x ↦ t * x) '' (F : Set G)))
    (x : ReducedGroupCStar G) : distGL x ≤ reducedTwoNorm x := by
  by_contra hlt
  push_neg at hlt
  have hεpos : 0 < (distGL x - reducedTwoNorm x) / 3 := by linarith
  obtain ⟨m, c, γ, happrox⟩ := exists_translationSum_approx G x.property hεpos
  have hxy : ‖x - ∑ i : Fin m, c i • reducedLeftRegular G (γ i)‖
      < (distGL x - reducedTwoNorm x) / 3 := by
    have hcoe : ((∑ i : Fin m, c i • reducedLeftRegular G (γ i) : ReducedGroupCStar G) :
        GroupHilbert G →L[ℂ] GroupHilbert G) = ∑ i : Fin m, c i • leftRegularOperator G (γ i) := by
      rw [AddSubmonoidClass.coe_finsetSum]
      exact Finset.sum_congr rfl fun i _ => by rw [SetLike.val_smul]; rfl
    change ‖(x : GroupHilbert G →L[ℂ] GroupHilbert G)
        - ((∑ i : Fin m, c i • reducedLeftRegular G (γ i) : ReducedGroupCStar G) :
          GroupHilbert G →L[ℂ] GroupHilbert G)‖ < _
    rw [hcoe]
    exact happrox
  have h1 := distGL_le_distGL_add_norm_sub x (∑ i : Fin m, c i • reducedLeftRegular G (γ i))
  have h2 := distGL_le_reducedTwoNorm_finSum hDH c γ
  have h3 := reducedTwoNorm_le_add_norm_sub (∑ i : Fin m, c i • reducedLeftRegular G (γ i)) x
  rw [norm_sub_rev] at h3
  linarith

/-- **Step 3: a contraction with `‖b‖₂ ≥ 1` is unitary**, through the canonical faithful
trace. -/
theorem mem_unitary_of_norm_le_one_of_one_le_reducedTwoNorm {b : ReducedGroupCStar G}
    (hb : ‖b‖ ≤ 1) (h2 : 1 ≤ reducedTwoNorm b) : b ∈ unitary (ReducedGroupCStar G) := by
  have hnorm2 : ‖(b : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)‖ = 1 :=
    le_antisymm ((reducedTwoNorm_le_norm b).trans hb) h2
  have hkill : ∀ P : ReducedGroupCStar G, 0 ≤ P → canonicalCoefficientAtOne G P = 0 →
      P = 0 := by
    intro P hP hτP
    have hsq : star (CFC.sqrt P) * CFC.sqrt P = P := by
      rw [(CFC.sqrt_nonneg P).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self P hP]
    have hz : CFC.sqrt P = 0 :=
      (canonicalFaithfulTracialState G).eq_zero_of_map_star_mul_self_eq_zero (by
        change canonicalCoefficientAtOne G (star (CFC.sqrt P) * CFC.sqrt P) = 0
        rw [hsq]
        exact hτP)
    rw [← hsq, hz, star_zero, zero_mul]
  have hnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ algebraMap ℝ (ReducedGroupCStar G) r := by
    intro r hr
    have e : algebraMap ℝ (ReducedGroupCStar G) r
        = star (algebraMap ℝ (ReducedGroupCStar G) (Real.sqrt r))
          * algebraMap ℝ (ReducedGroupCStar G) (Real.sqrt r) := by
      rw [← algebraMap_star_comm, star_trivial, ← map_mul, Real.mul_self_sqrt hr]
    rw [e]
    exact star_mul_self_nonneg _
  have hr0 : 0 ≤ 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  have htrace1 : canonicalCoefficientAtOne G 1 = 1 := (canonicalFaithfulTracialState G).map_one
  have hbb : star b * b = 1 := by
    have hP : 0 ≤ 1 - star b * b := by
      have hsum : 1 - star b * b = algebraMap ℝ (ReducedGroupCStar G) (1 - ‖b‖ ^ 2)
          + (algebraMap ℝ (ReducedGroupCStar G) (‖b‖ ^ 2) - star b * b) := by
        rw [map_sub, map_one]
        abel
      rw [hsum]
      exact add_nonneg (hnn _ hr0) (sub_nonneg.mpr CStarAlgebra.star_mul_le_algebraMap_norm_sq)
    have hτP : canonicalCoefficientAtOne G (1 - star b * b) = 0 := by
      rw [map_sub, canonicalCoefficientAtOne_star_mul_self, hnorm2, htrace1]
      simp
    exact (sub_eq_zero.mp (hkill _ hP hτP)).symm
  have hbbs : b * star b = 1 := by
    have hP : 0 ≤ 1 - b * star b := by
      have hsum : 1 - b * star b = algebraMap ℝ (ReducedGroupCStar G) (1 - ‖b‖ ^ 2)
          + (algebraMap ℝ (ReducedGroupCStar G) (‖b‖ ^ 2) - b * star b) := by
        rw [map_sub, map_one]
        abel
      rw [hsum]
      exact add_nonneg (hnn _ hr0) (sub_nonneg.mpr CStarAlgebra.mul_star_le_algebraMap_norm_sq)
    have hτP : canonicalCoefficientAtOne G (1 - b * star b) = 0 := by
      rw [map_sub, canonicalCoefficientAtOne_mul_comm G b (star b),
        canonicalCoefficientAtOne_star_mul_self, hnorm2, htrace1]
      simp
    exact (sub_eq_zero.mp (hkill _ hP hτP)).symm
  exact Unitary.mem_iff.mpr ⟨hbb, hbbs⟩

/-- **Dykema–de la Harpe, Theorem 1.4** (Gerasimova–Osin's Theorem 5.4), proved. -/
theorem dykemaDeLaHarpeTheorem14 : DykemaDeLaHarpeTheorem14 := by
  intro G _ hDH
  show Dense {x : ReducedGroupCStar G | IsUnit x}
  by_contra hns
  obtain ⟨b, hb1, hdb⟩ :=
    RordamDistanceOne.exists_norm_eq_one_distGL_eq_one (A := ReducedGroupCStar G) hns
  have h2 : 1 ≤ reducedTwoNorm b := by
    have h := distGL_le_reducedTwoNorm hDH b
    rwa [hdb] at h
  have hu := mem_unitary_of_norm_le_one_of_one_le_reducedTwoNorm hb1.le h2
  have h0 : distGL b = 0 :=
    Metric.infDist_zero_of_mem (mem_invertibles.mpr (isUnit_of_mem_unitary hu))
  linarith

/-- **`GerasimovaOsinTheorem11Printed` from the geometric input alone.** -/
theorem gerasimovaOsinTheorem11Printed_of_freeSubsemigroupInput
    (hGO : GerasimovaOsinFreeSubsemigroupInput) : GerasimovaOsinTheorem11Printed :=
  gerasimovaOsinTheorem11Printed_of_inputs dykemaDeLaHarpeTheorem14 hGO

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms distGL_le_reducedTwoNorm_finSum
#audit_axioms distGL_le_reducedTwoNorm
#audit_axioms mem_unitary_of_norm_le_one_of_one_le_reducedTwoNorm
#audit_closed_axioms dykemaDeLaHarpeTheorem14
#audit_axioms gerasimovaOsinTheorem11Printed_of_freeSubsemigroupInput
