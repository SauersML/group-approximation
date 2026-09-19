import GroupApproximation.Analysis.PolarLiftingGeneralCStar
import GroupApproximation.Sofic.InvolutionRankMass

/-!
# Exact covariance correction for a finite packet

Let `φ` and `ψ` be two unitary representations of a finite group in a
unital C-star algebra.  The Reynolds average

`T = |F|⁻¹ ∑ f, ψ(f) φ(f)⋆`

is an exact intertwiner.  If `T` is sufficiently close to unitary, its polar
unitary is still an exact intertwiner.  This is the dimension-independent
finite-packet correction used by the noncommutative packet collapse route.

The file deliberately separates the algebraic statement from the later
corona exactification step: no approximate representation or unproved
stability principle occurs here.
-/

namespace GroupApproximation
namespace FinitePacketCovariance

open PolarLiftingGeneralCStar

noncomputable section

universe u v

variable {F : Type u} [Group F]
variable {A : Type v} [CStarAlgebra A]

/-- The normalized finite-group average of the pointwise intertwiners. -/
noncomputable def averagedIntertwiner
    [Fintype F] (φ ψ : F →* unitary A) : A :=
  ((Fintype.card F : ℂ)⁻¹) •
    ∑ f : F, ((ψ f : unitary A) : A) * star ((φ f : unitary A) : A)

/-- The summand obtained after left-translating the finite-group index. -/
private theorem translated_summand (φ ψ : F →* unitary A) (g x : F) :
    ((ψ (g * x) : unitary A) : A) * star ((φ (g * x) : unitary A) : A) *
        ((φ g : unitary A) : A) =
      ((ψ g : unitary A) : A) *
        (((ψ x : unitary A) : A) * star ((φ x : unitary A) : A)) := by
  have hφ : star ((φ g : unitary A) : A) * ((φ g : unitary A) : A) = 1 :=
    Unitary.star_mul_self_of_mem (φ g).prop
  simp only [map_mul]
  change (((ψ g : unitary A) : A) * ((ψ x : unitary A) : A)) *
      star (((φ g : unitary A) : A) * ((φ x : unitary A) : A)) *
        ((φ g : unitary A) : A) = _
  rw [star_mul]
  calc
    (((ψ g : unitary A) : A) * ((ψ x : unitary A) : A)) *
          (star ((φ x : unitary A) : A) * star ((φ g : unitary A) : A)) *
            ((φ g : unitary A) : A) =
        ((ψ g : unitary A) : A) * ((ψ x : unitary A) : A) *
          star ((φ x : unitary A) : A) *
            (star ((φ g : unitary A) : A) * ((φ g : unitary A) : A)) := by
              noncomm_ring
    _ = ((ψ g : unitary A) : A) *
        (((ψ x : unitary A) : A) * star ((φ x : unitary A) : A)) := by
      rw [hφ, mul_one, mul_assoc]

/-- The averaged operator exactly intertwines the two representations. -/
theorem averagedIntertwiner_mul [Fintype F]
    (φ ψ : F →* unitary A) (g : F) :
    averagedIntertwiner φ ψ * ((φ g : unitary A) : A) =
      ((ψ g : unitary A) : A) * averagedIntertwiner φ ψ := by
  classical
  unfold averagedIntertwiner
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  rw [Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ f : F, (((ψ f : unitary A) : A) * star ((φ f : unitary A) : A)) *
        ((φ g : unitary A) : A)) =
        ∑ x : F, (((ψ (g * x) : unitary A) : A) *
          star ((φ (g * x) : unitary A) : A)) *
            ((φ g : unitary A) : A) := by
          symm
          exact Fintype.sum_equiv (Equiv.mulLeft g)
            (fun x : F ↦ (((ψ (g * x) : unitary A) : A) *
              star ((φ (g * x) : unitary A) : A)) *
                ((φ g : unitary A) : A))
            (fun f : F ↦ (((ψ f : unitary A) : A) *
              star ((φ f : unitary A) : A)) * ((φ g : unitary A) : A))
            (fun _ ↦ rfl)
    _ = ∑ x : F, ((ψ g : unitary A) : A) *
          (((ψ x : unitary A) : A) * star ((φ x : unitary A) : A)) := by
      exact Finset.sum_congr rfl fun x _ ↦ translated_summand φ ψ g x

/-- The average is close to `1` whenever every pointwise intertwiner is.
This form avoids imposing a particular approximation modulus. -/
theorem norm_averagedIntertwiner_sub_one_le
    [Fintype F] (φ ψ : F →* unitary A) (ε : ℝ)
    (hclose : ∀ f : F,
      ‖((ψ f : unitary A) : A) * star ((φ f : unitary A) : A) - 1‖ ≤ ε) :
    ‖averagedIntertwiner φ ψ - 1‖ ≤ ε := by
  classical
  have hcard : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card F ≠ 0)
  have hrewrite : averagedIntertwiner φ ψ - 1 =
      ((Fintype.card F : ℂ)⁻¹) •
        ∑ f : F,
          (((ψ f : unitary A) : A) * star ((φ f : unitary A) : A) - 1) := by
    unfold averagedIntertwiner
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_sub]
    rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [hrewrite, norm_smul]
  calc
    ‖((Fintype.card F : ℂ)⁻¹)‖ *
          ‖∑ f : F, (((ψ f : unitary A) : A) *
            star ((φ f : unitary A) : A) - 1)‖
        ≤ ‖((Fintype.card F : ℂ)⁻¹)‖ *
            ∑ f : F, ‖((ψ f : unitary A) : A) *
              star ((φ f : unitary A) : A) - 1‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖((Fintype.card F : ℂ)⁻¹)‖ *
          ∑ _f : F, ε :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun f _ ↦ hclose f) (norm_nonneg _)
    _ = ε := by
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
      simp only [norm_inv, Complex.norm_natCast, smul_eq_mul]
      have hc : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp

/-- If `x` intertwines `φ` with `ψ`, then its Gram element commutes with
`φ(g)`. -/
theorem gram_commutes_of_intertwines
    (φ ψ : F →* unitary A) {x : A}
    (hinter : ∀ g : F,
      x * ((φ g : unitary A) : A) = ((ψ g : unitary A) : A) * x)
    (g : F) :
    Commute (star x * x) ((φ g : unitary A) : A) := by
  have h := hinter g
  have hinv := hinter g⁻¹
  have hφinv : ((φ g⁻¹ : unitary A) : A) = star ((φ g : unitary A) : A) := by
    rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
  have hψinv : ((ψ g⁻¹ : unitary A) : A) = star ((ψ g : unitary A) : A) := by
    rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
  rw [hφinv, hψinv] at hinv
  have hstar : ((φ g : unitary A) : A) * star x =
      star x * ((ψ g : unitary A) : A) := by
    have := congrArg star hinv
    simpa only [star_mul, star_star] using this
  rw [Commute]
  calc
    star x * x * ((φ g : unitary A) : A) =
        star x * (((ψ g : unitary A) : A) * x) := by rw [mul_assoc, h]
    _ = ((φ g : unitary A) : A) * (star x * x) := by
      rw [← mul_assoc, ← hstar, mul_assoc]

/-- The inverse square root of the Gram element still commutes with the
source representation. -/
theorem polarInvSqrt_commutes_of_intertwines
    (φ ψ : F →* unitary A) {x : A}
    (hinter : ∀ g : F,
      x * ((φ g : unitary A) : A) = ((ψ g : unitary A) : A) * x)
    (g : F) :
    Commute (polarInvSqrt x) ((φ g : unitary A) : A) := by
  exact (IsSelfAdjoint.star_mul_self x).commute_cfc
    (gram_commutes_of_intertwines φ ψ hinter g)
    invSqrt

/-- Polar correction preserves an exact intertwining relation. -/
theorem polarUnitary_mul_of_intertwines
    (φ ψ : F →* unitary A) {x : A}
    (hinter : ∀ g : F,
      x * ((φ g : unitary A) : A) = ((ψ g : unitary A) : A) * x)
    (g : F) :
    polarUnitary x * ((φ g : unitary A) : A) =
      ((ψ g : unitary A) : A) * polarUnitary x := by
  unfold polarUnitary
  have hc := polarInvSqrt_commutes_of_intertwines φ ψ hinter g
  calc
    x * polarInvSqrt x * ((φ g : unitary A) : A) =
        x * (((φ g : unitary A) : A) * polarInvSqrt x) := by
          rw [mul_assoc, hc.eq]
    _ = ((ψ g : unitary A) : A) * (x * polarInvSqrt x) := by
      rw [← mul_assoc, hinter g, mul_assoc]

/-- The polar unitary of the averaged intertwiner exactly conjugates `φ` to
`ψ`, provided the two standard Gram bounds hold. -/
theorem polar_corrected_covariance
    [Fintype F] (φ ψ : F →* unitary A)
    (hleft : ‖star (averagedIntertwiner φ ψ) * averagedIntertwiner φ ψ - 1‖ ≤ 1 / 2)
    (hright : ‖averagedIntertwiner φ ψ * star (averagedIntertwiner φ ψ) - 1‖ ≤ 1 / 2) :
    ∃ z : unitary A, ∀ g : F,
      ((z : unitary A) : A) * ((φ g : unitary A) : A) *
          star ((z : unitary A) : A) = ((ψ g : unitary A) : A) := by
  let z : unitary A :=
    ⟨polarUnitary (averagedIntertwiner φ ψ),
      polarUnitary_mem_unitary hleft hright⟩
  refine ⟨z, fun g ↦ ?_⟩
  have hinter := averagedIntertwiner_mul φ ψ
  have hz := polarUnitary_mul_of_intertwines φ ψ hinter g
  have hzz : ((z : unitary A) : A) * star ((z : unitary A) : A) = 1 :=
    Unitary.mul_star_self_of_mem z.prop
  change polarUnitary (averagedIntertwiner φ ψ) *
      ((φ g : unitary A) : A) *
        star (polarUnitary (averagedIntertwiner φ ψ)) = _
  have hzz' : polarUnitary (averagedIntertwiner φ ψ) *
      star (polarUnitary (averagedIntertwiner φ ψ)) = 1 := hzz
  rw [hz, mul_assoc, hzz', mul_one]

/-- Being close to `1` controls the left Gram defect. -/
theorem norm_star_mul_self_sub_one_le_of_norm_sub_one_le
    [Nontrivial A] {x : A} {ε : ℝ} (hε : 0 ≤ ε) (hx : ‖x - 1‖ ≤ ε) :
    ‖star x * x - 1‖ ≤ ε * (2 + ε) := by
  have hxnorm : ‖x‖ ≤ 1 + ε := by
    calc
      ‖x‖ = ‖(x - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - 1‖ + ‖(1 : A)‖ := norm_add_le _ _
      _ ≤ ε + 1 := by rw [norm_one]; linarith
      _ = 1 + ε := by ring
  have hid : star x * x - 1 = star (x - 1) * x + (x - 1) := by
    rw [star_sub, star_one]
    noncomm_ring
  rw [hid]
  calc
    ‖star (x - 1) * x + (x - 1)‖ ≤
        ‖star (x - 1) * x‖ + ‖x - 1‖ := norm_add_le _ _
    _ ≤ ‖star (x - 1)‖ * ‖x‖ + ‖x - 1‖ := by
      gcongr
      exact norm_mul_le _ _
    _ = ‖x - 1‖ * ‖x‖ + ‖x - 1‖ := by rw [norm_star]
    _ ≤ ε * (1 + ε) + ε := by
      have hxn := norm_nonneg x
      have hdn := norm_nonneg (x - 1)
      nlinarith
    _ = ε * (2 + ε) := by ring

/-- Being close to `1` also controls the right Gram defect. -/
theorem norm_mul_star_self_sub_one_le_of_norm_sub_one_le
    [Nontrivial A] {x : A} {ε : ℝ} (hε : 0 ≤ ε) (hx : ‖x - 1‖ ≤ ε) :
    ‖x * star x - 1‖ ≤ ε * (2 + ε) := by
  have hxstar : ‖star x - 1‖ ≤ ε := by
    rw [← star_one, ← star_sub, norm_star]
    exact hx
  simpa only [star_star] using
    norm_star_mul_self_sub_one_le_of_norm_sub_one_le hε hxstar

/-- Closeness to an arbitrary unitary controls the left Gram defect with the
same dimension-free estimate as closeness to `1`. -/
theorem norm_star_mul_self_sub_one_le_of_norm_sub_unitary_le
    [Nontrivial A] {x u : A} (hu : u ∈ unitary A) {ε : ℝ}
    (hε : 0 ≤ ε) (hx : ‖x - u‖ ≤ ε) :
    ‖star x * x - 1‖ ≤ ε * (2 + ε) := by
  let y : A := x * star u
  have hy : ‖y - 1‖ ≤ ε := by
    have hunit : u * star u = 1 := Unitary.mul_star_self_of_mem hu
    have hid : y - 1 = (x - u) * star u := by
      dsimp [y]
      rw [sub_mul, hunit]
    rw [hid, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hu)]
    exact hx
  have hbase := norm_star_mul_self_sub_one_le_of_norm_sub_one_le hε hy
  have hconj : star y * y - 1 = u * (star x * x - 1) * star u := by
    dsimp [y]
    rw [star_mul, star_star]
    noncomm_ring [Unitary.mul_star_self_of_mem hu]
  rw [hconj] at hbase
  calc
    ‖star x * x - 1‖ = ‖u * (star x * x - 1)‖ :=
      (CStarRing.norm_mem_unitary_mul _ hu).symm
    _ = ‖u * (star x * x - 1) * star u‖ :=
      (CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hu)).symm
    _ ≤ ε * (2 + ε) := hbase

/-- Closeness to an arbitrary unitary controls the right Gram defect. -/
theorem norm_mul_star_self_sub_one_le_of_norm_sub_unitary_le
    [Nontrivial A] {x u : A} (hu : u ∈ unitary A) {ε : ℝ}
    (hε : 0 ≤ ε) (hx : ‖x - u‖ ≤ ε) :
    ‖x * star x - 1‖ ≤ ε * (2 + ε) := by
  have hxstar : ‖star x - star u‖ ≤ ε := by
    rw [← star_sub, norm_star]
    exact hx
  simpa only [star_star] using
    norm_star_mul_self_sub_one_le_of_norm_sub_unitary_le
      (Unitary.star_mem hu) hε hxstar

/-- A point within `1/8` of a unitary has a well-defined unitary polar
correction. -/
theorem polarUnitary_mem_unitary_of_norm_sub_unitary_le
    [Nontrivial A] {x u : A} (hu : u ∈ unitary A) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8) (hx : ‖x - u‖ ≤ ε) :
    polarUnitary x ∈ unitary A := by
  have hsmall : ε * (2 + ε) ≤ 1 / 2 := by nlinarith
  exact polarUnitary_mem_unitary
    ((norm_star_mul_self_sub_one_le_of_norm_sub_unitary_le hu hε0 hx).trans hsmall)
    ((norm_mul_star_self_sub_one_le_of_norm_sub_unitary_le hu hε0 hx).trans hsmall)

/-- The unitary polar correction stays within `6ε` of the nearby unitary. -/
theorem norm_polarUnitary_sub_unitary_le
    [Nontrivial A] {x u : A} (hu : u ∈ unitary A) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8) (hx : ‖x - u‖ ≤ ε) :
    ‖polarUnitary x - u‖ ≤ 6 * ε := by
  have hgram0 : ‖star x * x - 1‖ ≤ ε * (2 + ε) :=
    norm_star_mul_self_sub_one_le_of_norm_sub_unitary_le hu hε0 hx
  have hsmall : ε * (2 + ε) ≤ 1 / 2 := by nlinarith
  have hgram : ‖star x * x - 1‖ ≤ 1 / 2 := hgram0.trans hsmall
  have hxnorm : ‖x‖ ≤ 1 + ε := by
    have hunorm : ‖u‖ = 1 := CStarRing.norm_of_mem_unitary hu
    calc
      ‖x‖ = ‖(x - u) + u‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - u‖ + ‖u‖ := norm_add_le _ _
      _ ≤ ε + 1 := by rw [hunorm]; linarith
      _ = 1 + ε := by ring
  calc
    ‖polarUnitary x - u‖ ≤ ‖polarUnitary x - x‖ + ‖x - u‖ := by
      have hid : polarUnitary x - u = (polarUnitary x - x) + (x - u) := by abel
      rw [hid]
      exact norm_add_le _ _
    _ ≤ 2 * ‖x‖ * ‖star x * x - 1‖ + ε :=
      add_le_add (norm_polarUnitary_sub_le hgram) hx
    _ ≤ 2 * (1 + ε) * (ε * (2 + ε)) + ε := by
      have hxnonneg := norm_nonneg x
      have hgnonneg := norm_nonneg (star x * x - 1)
      nlinarith
    _ ≤ 6 * ε := by
      have hcoef : 2 * (1 + ε) * (2 + ε) + 1 ≤ 6 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hcoef hε0
      nlinarith

/-- **Finite-packet covariance correction, quantitative form.**

If the two exact finite-group representations differ pointwise by at most
`ε ≤ 1/8`, finite averaging followed by polar decomposition produces a
unitary `z` with exact covariance and `‖z - 1‖ ≤ 6 ε`.  The constants are
uniform in the target C-star algebra and, in particular, in matrix size. -/
theorem exists_near_identity_exact_covariance
    [Fintype F] [Nontrivial A] (φ ψ : F →* unitary A) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8)
    (hclose : ∀ f : F,
      ‖((ψ f : unitary A) : A) * star ((φ f : unitary A) : A) - 1‖ ≤ ε) :
    ∃ z : unitary A,
      ‖((z : unitary A) : A) - 1‖ ≤ 6 * ε ∧
      ∀ g : F,
        ((z : unitary A) : A) * ((φ g : unitary A) : A) *
            star ((z : unitary A) : A) = ((ψ g : unitary A) : A) := by
  let T : A := averagedIntertwiner φ ψ
  have hT : ‖T - 1‖ ≤ ε :=
    norm_averagedIntertwiner_sub_one_le φ ψ ε hclose
  have hleft0 : ‖star T * T - 1‖ ≤ ε * (2 + ε) :=
    norm_star_mul_self_sub_one_le_of_norm_sub_one_le hε0 hT
  have hright0 : ‖T * star T - 1‖ ≤ ε * (2 + ε) :=
    norm_mul_star_self_sub_one_le_of_norm_sub_one_le hε0 hT
  have hsmall : ε * (2 + ε) ≤ 1 / 2 := by nlinarith
  have hleft : ‖star T * T - 1‖ ≤ 1 / 2 := hleft0.trans hsmall
  have hright : ‖T * star T - 1‖ ≤ 1 / 2 := hright0.trans hsmall
  let z : unitary A :=
    ⟨polarUnitary T, polarUnitary_mem_unitary hleft hright⟩
  refine ⟨z, ?_, ?_⟩
  · change ‖polarUnitary T - 1‖ ≤ 6 * ε
    calc
      ‖polarUnitary T - 1‖ ≤ ‖polarUnitary T - T‖ + ‖T - 1‖ := by
        have hid : polarUnitary T - 1 = (polarUnitary T - T) + (T - 1) := by abel
        rw [hid]
        exact norm_add_le _ _
      _ ≤ 2 * ‖T‖ * ‖star T * T - 1‖ + ε := by
        exact add_le_add (norm_polarUnitary_sub_le hleft) hT
      _ ≤ 2 * (1 + ε) * (ε * (2 + ε)) + ε := by
        have hTnorm : ‖T‖ ≤ 1 + ε := by
          calc
            ‖T‖ = ‖(T - 1) + 1‖ := by rw [sub_add_cancel]
            _ ≤ ‖T - 1‖ + ‖(1 : A)‖ := norm_add_le _ _
            _ ≤ ε + 1 := by rw [norm_one]; linarith
            _ = 1 + ε := by ring
        have hTnonneg := norm_nonneg T
        have hgramnonneg := norm_nonneg (star T * T - 1)
        nlinarith
      _ ≤ 6 * ε := by
        have hcoef : 2 * (1 + ε) * (2 + ε) + 1 ≤ 6 := by nlinarith
        have hmul := mul_le_mul_of_nonneg_left hcoef hε0
        nlinarith
  · intro g
    have hinter : ∀ h : F,
        T * ((φ h : unitary A) : A) = ((ψ h : unitary A) : A) * T :=
      averagedIntertwiner_mul φ ψ
    have hz := polarUnitary_mul_of_intertwines φ ψ hinter g
    have hzz : polarUnitary T * star (polarUnitary T) = 1 :=
      Unitary.mul_star_self_of_mem z.prop
    change polarUnitary T * ((φ g : unitary A) : A) *
        star (polarUnitary T) = _
    rw [hz, mul_assoc, hzz, mul_one]

end

end FinitePacketCovariance
end GroupApproximation
