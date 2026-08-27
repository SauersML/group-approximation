import GroupApproximation.Kazhdan.UltralimitGeometry
import GroupApproximation.Kazhdan.DelormeFixedPoint

/-!
# Scalar Delorme at the ultralimit

An analytic collapse argument produces, on a Kazhdan group `G`, a
sequence of maps `b k : G → H k` into real inner product spaces which are
cocycles only approximately: no single stage `k` carries a genuine
orbit-map identity, and only the standard-part profile

  `ψ̄ g = st ‖b k g‖ ^ 2`

satisfies `ψ̄ (g⁻¹ * h) = st ‖b k h - b k g‖ ^ 2`.  This module supplies
the boundedness of `ψ̄`.

The obstruction to reusing `GaussianPositiveDefinite` stagewise is that
`g ↦ exp (-t * ‖b k g‖ ^ 2)` need not be a positive-definite function on
the group at any fixed stage; only the two-variable *displacement kernel*
`exp (-t * ‖b k j - b k i‖ ^ 2)` is positive semidefinite there, which is
what `gaussianDisplacement_quadForm_nonneg` isolates from the Gram/Schur
machinery.  Positive-definiteness of the group kernel is then recovered
only in the limit: each finite quadratic form of `exp (-t * ψ̄)` is the
standard part of the corresponding stagewise displacement form, because
the sum is finite and the standard part is a ring homomorphism on limited
hyperreals.  Delorme's Gaussian boundedness principle
(`Delorme.bounded_of_gaussian_isPositiveDefinite`) then bounds `ψ̄`.
-/

open scoped Matrix InnerProductSpace

namespace GroupApproximation
namespace UltralimitGaussian

open KazhdanFiniteModel Ultralimit

universe u v

section GramKernel

variable {ι : Type*} [Fintype ι]

/-- Extract nonnegativity of the real quadratic form, written as a double
sum, from positive semidefiniteness of a matrix. -/
private theorem quadForm_nonneg_of_posSemidef {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (x : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * x j * A i j := by
  have hdot : star x ⬝ᵥ (A *ᵥ x) = ∑ i, ∑ j, x i * x j * A i j := by
    simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ by ring
  have h := hA.dotProduct_mulVec_nonneg x
  rwa [hdot] at h

/-- **The Gaussian displacement kernel is positive semidefinite.**  For a
finite family of vectors `v` in a real inner product space and `0 ≤ t`,
the two-variable kernel `exp (-t * ‖v j - v i‖ ^ 2)` has nonnegative real
quadratic forms.  The factorization
`exp (-t‖v j - v i‖ ^ 2) =
  exp (-t‖v i‖ ^ 2) * exp ⟪√(2t) v i, √(2t) v j⟫ * exp (-t‖v j‖ ^ 2)`
reduces the form to that of the entrywise exponential of a Gram matrix at
rescaled coefficients, which is positive semidefinite by
`GaussianKernel.posSemidef_gram` and
`GaussianKernel.posSemidef_exp_entry`.

This is the kernel-level content of
`GaussianKernel.isPositiveDefinite_exp_neg_norm_sq`, stated without a
group: the sequences pushed to the ultralimit below are only
almost-cocycles, so no stage carries a genuine group kernel. -/
theorem gaussianDisplacement_quadForm_nonneg {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ι → E)
    (x : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∑ i, ∑ j, x i * x j * Real.exp (-t * ‖v j - v i‖ ^ 2) := by
  have hfact : ∀ i j : ι, Real.exp (-t * ‖v j - v i‖ ^ 2) =
      Real.exp (-t * ‖v i‖ ^ 2) *
        Real.exp (⟪Real.sqrt (2 * t) • v i,
          Real.sqrt (2 * t) • v j⟫_ℝ) *
        Real.exp (-t * ‖v j‖ ^ 2) := by
    intro i j
    rw [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [← mul_assoc, Real.mul_self_sqrt (by linarith),
      real_inner_comm (v j) (v i)]
    ring
  have heq : ∑ i, ∑ j, x i * x j * Real.exp (-t * ‖v j - v i‖ ^ 2) =
      ∑ i, ∑ j,
        (x i * Real.exp (-t * ‖v i‖ ^ 2)) *
          (x j * Real.exp (-t * ‖v j‖ ^ 2)) *
          Real.exp (⟪Real.sqrt (2 * t) • v i,
            Real.sqrt (2 * t) • v j⟫_ℝ) := by
    refine Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hfact i j]
    ring
  have hgram := quadForm_nonneg_of_posSemidef
    (GaussianKernel.posSemidef_exp_entry
      (GaussianKernel.posSemidef_gram
        fun i : ι ↦ Real.sqrt (2 * t) • v i))
    (fun i : ι ↦ x i * Real.exp (-t * ‖v i‖ ^ 2))
  rw [heq]
  simpa [Matrix.of_apply] using hgram

/-- The `Finset`-indexed form of `gaussianDisplacement_quadForm_nonneg`:
the displacement kernel of any family of vectors indexed by a group has
nonnegative quadratic forms over every finite subset. -/
theorem gaussianDisplacement_sum_nonneg {α : Type*} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (F : Finset α)
    (c : α → ℝ) (v : α → E) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∑ i ∈ F, ∑ j ∈ F,
      c i * c j * Real.exp (-t * ‖v j - v i‖ ^ 2) := by
  have heq : ∑ i ∈ F, ∑ j ∈ F,
      c i * c j * Real.exp (-t * ‖v j - v i‖ ^ 2) =
      ∑ p : F, ∑ q : F,
        c ↑p * c ↑q * Real.exp (-t * ‖v ↑q - v ↑p‖ ^ 2) := by
    rw [← Finset.sum_coe_sort F]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.sum_coe_sort F]
  rw [heq]
  exact gaussianDisplacement_quadForm_nonneg (fun p : F ↦ v ↑p)
    (fun p : F ↦ c ↑p) ht

end GramKernel

section Profile

variable {G : Type u} [Group G] {H : ℕ → Type v}
  [∀ k, NormedAddCommGroup (H k)] [∀ k, InnerProductSpace ℝ (H k)]

omit [∀ k, InnerProductSpace ℝ (H k)] in
/-- A sequence of vectors with uniformly bounded squared norms is a
bounded sequence in the sense of `Ultralimit.IsBoundedSeq`. -/
theorem isBoundedSeq_of_normSq_le {v : ∀ k, H k}
    (h : ∃ C : ℝ, ∀ k, ‖v k‖ ^ 2 ≤ C) : IsBoundedSeq v := by
  obtain ⟨C, hC⟩ := h
  refine ⟨Real.sqrt C, fun k ↦ ?_⟩
  have hle : Real.sqrt (‖v k‖ ^ 2) ≤ Real.sqrt C :=
    Real.sqrt_le_sqrt (hC k)
  rwa [Real.sqrt_sq (norm_nonneg (v k))] at hle

omit [∀ k, InnerProductSpace ℝ (H k)] in
/-- **Gaussians commute with the ultralimit.**  For a bounded sequence of
vectors and `0 ≤ t`, the standard part of the stagewise Gaussian is the
Gaussian of the limiting squared seminorm. -/
theorem stdPart_exp_neg_mul_normSq {v : ∀ k, H k} (hv : IsBoundedSeq v)
    {t : ℝ} (ht : 0 ≤ t) :
    ArchimedeanClass.stdPart
        (Hyperreal.ofSeq fun k ↦ Real.exp (-t * ‖v k‖ ^ 2)) =
      Real.exp (-t * seqNormSq v) := by
  obtain ⟨C, hC⟩ := id hv
  have hup : ∀ k, -t * ‖v k‖ ^ 2 ≤ 0 := by
    intro k
    have h0 : 0 ≤ ‖v k‖ ^ 2 := sq_nonneg _
    linarith [mul_nonneg ht h0]
  have hdown : ∀ k, -t * C ^ 2 ≤ -t * ‖v k‖ ^ 2 := by
    intro k
    have h0 : 0 ≤ ‖v k‖ := norm_nonneg (v k)
    have hsq : ‖v k‖ ^ 2 ≤ C ^ 2 := by nlinarith [hC k]
    linarith [mul_le_mul_of_nonneg_left hsq ht]
  have hstd := stdPart_exp (s := fun k ↦ -t * ‖v k‖ ^ 2) hdown hup
  rw [hstd]
  congr 1
  have hmul : (Hyperreal.ofSeq fun k ↦ -t * ‖v k‖ ^ 2) =
      ((-t : ℝ) : Hyperreal) *
        (Hyperreal.ofSeq fun k ↦ ‖v k‖ ^ 2) := by
    rw [show ((-t : ℝ) : Hyperreal) =
      Hyperreal.ofSeq (fun _ : ℕ ↦ (-t : ℝ)) from rfl, ← ofSeq_mul]
  rw [hmul, ArchimedeanClass.stdPart_mul (hyperreal_coe_finite (-t))
    (ofSeq_norm_sq_finite hv), stdPart_coe, seqNormSq_def]

/-- The standard-part profile of a sequence of almost-cocycles: the
ultralimit of the stagewise squared displacements. -/
noncomputable def profile (b : ∀ k, G → H k) (g : G) : ℝ :=
  seqNormSq fun k ↦ b k g

omit [Group G] [∀ k, InnerProductSpace ℝ (H k)] in
/-- The profile, unfolded to the hyperreal standard part it abbreviates. -/
theorem profile_eq (b : ∀ k, G → H k) (g : G) :
    profile b g =
      ArchimedeanClass.stdPart
        (Hyperreal.ofSeq fun k ↦ ‖b k g‖ ^ 2) :=
  seqNormSq_def _

omit [∀ k, InnerProductSpace ℝ (H k)] in
/-- The profile vanishes at the identity. -/
theorem profile_one {b : ∀ k, G → H k} (hone : ∀ k, b k 1 = 0) :
    profile b 1 = 0 := by
  have hconst : (Hyperreal.ofSeq fun k ↦ ‖b k (1 : G)‖ ^ 2) =
      ((0 : ℝ) : Hyperreal) := by
    rw [show (fun k ↦ ‖b k (1 : G)‖ ^ 2) = fun _ : ℕ ↦ (0 : ℝ) from by
      funext k
      rw [hone k, norm_zero]
      ring]
    rfl
  rw [profile_eq, hconst, stdPart_coe]

omit [Group G] [∀ k, InnerProductSpace ℝ (H k)] in
/-- The profile is nonnegative: it is the square of a limiting
seminorm. -/
theorem profile_nonneg {b : ∀ k, G → H k}
    (hbdd : ∀ g : G, ∃ C : ℝ, ∀ k, ‖b k g‖ ^ 2 ≤ C) (g : G) :
    0 ≤ profile b g := by
  have hsq : profile b g = seqNorm (fun k ↦ b k g) ^ 2 :=
    seqNormSq_eq_sq (isBoundedSeq_of_normSq_le (hbdd g))
  rw [hsq]
  exact sq_nonneg _

omit [∀ k, InnerProductSpace ℝ (H k)] in
/-- The symmetry `ψ̄ (g⁻¹ * h) = ψ̄ (h⁻¹ * g)` required of a
positive-definite kernel, read off from the limiting displacement
identity and `norm_sub_rev`. -/
theorem profile_inv_mul_comm {b : ∀ k, G → H k}
    (halmost : ∀ g h : G,
      ArchimedeanClass.stdPart
          (Hyperreal.ofSeq fun k ↦ ‖b k (g⁻¹ * h)‖ ^ 2) =
        ArchimedeanClass.stdPart
          (Hyperreal.ofSeq fun k ↦ ‖b k h - b k g‖ ^ 2))
    (g h : G) : profile b (g⁻¹ * h) = profile b (h⁻¹ * g) := by
  rw [profile_eq, profile_eq, halmost g h, halmost h g]
  congr 1
  apply congrArg Hyperreal.ofSeq
  funext k
  rw [norm_sub_rev]

omit [∀ k, InnerProductSpace ℝ (H k)] in
/-- Each Gaussian entry of the limiting group kernel is the standard part
of the stagewise displacement kernel. -/
theorem exp_neg_mul_profile_eq {b : ∀ k, G → H k}
    (hbdd : ∀ g : G, ∃ C : ℝ, ∀ k, ‖b k g‖ ^ 2 ≤ C)
    (halmost : ∀ g h : G,
      ArchimedeanClass.stdPart
          (Hyperreal.ofSeq fun k ↦ ‖b k (g⁻¹ * h)‖ ^ 2) =
        ArchimedeanClass.stdPart
          (Hyperreal.ofSeq fun k ↦ ‖b k h - b k g‖ ^ 2))
    {t : ℝ} (ht : 0 ≤ t) (g h : G) :
    Real.exp (-t * profile b (g⁻¹ * h)) =
      ArchimedeanClass.stdPart
        (Hyperreal.ofSeq fun k ↦
          Real.exp (-t * ‖b k h - b k g‖ ^ 2)) := by
  have hsub : IsBoundedSeq (fun k ↦ b k h - b k g) :=
    (isBoundedSeq_of_normSq_le (hbdd h)).sub
      (isBoundedSeq_of_normSq_le (hbdd g))
  have hd : profile b (g⁻¹ * h) = seqNormSq (fun k ↦ b k h - b k g) := by
    rw [profile_eq, seqNormSq_def]
    exact halmost g h
  rw [hd]
  exact (stdPart_exp_neg_mul_normSq hsub ht).symm

/-- **Positive-definiteness of the limiting Gaussian.**  Although no
stage carries a positive-definite group kernel, every finite quadratic
form of `g ↦ exp (-t * ψ̄ g)` is the standard part of the corresponding
stagewise displacement form, which is nonnegative by
`gaussianDisplacement_sum_nonneg`; the transfer is legitimate because the
sum is finite and the standard part is additive and multiplicative on
limited hyperreals. -/
theorem isPositiveDefinite_exp_neg_mul_profile {b : ∀ k, G → H k}
    (hbdd : ∀ g : G, ∃ C : ℝ, ∀ k, ‖b k g‖ ^ 2 ≤ C)
    (halmost : ∀ g h : G,
      ArchimedeanClass.stdPart
          (Hyperreal.ofSeq fun k ↦ ‖b k (g⁻¹ * h)‖ ^ 2) =
        ArchimedeanClass.stdPart
          (Hyperreal.ofSeq fun k ↦ ‖b k h - b k g‖ ^ 2))
    {t : ℝ} (ht : 0 ≤ t) :
    KazhdanFiniteModel.IsPositiveDefinite
      (fun g ↦ Real.exp (-t * profile b g)) := by
  classical
  constructor
  · intro g h
    show Real.exp (-t * profile b (g⁻¹ * h)) =
      Real.exp (-t * profile b (h⁻¹ * g))
    rw [profile_inv_mul_comm halmost g h]
  · intro F c
    show (0 : ℝ) ≤ ∑ i ∈ F, ∑ j ∈ F,
      c i * c j * Real.exp (-t * profile b (i⁻¹ * j))
    have hfin : ∀ i j : G, 0 ≤ ArchimedeanClass.mk
        (Hyperreal.ofSeq fun k ↦
          Real.exp (-t * ‖b k j - b k i‖ ^ 2)) := by
      intro i j
      refine ofSeq_finite_of_bounds
        (fun k ↦ (Real.exp_pos _).le) (b := 1) fun k ↦ ?_
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      refine Real.exp_le_exp.mpr ?_
      have h0 : 0 ≤ ‖b k j - b k i‖ ^ 2 := sq_nonneg _
      linarith [mul_nonneg ht h0]
    have hterm : ∀ i j : G,
        c i * c j * Real.exp (-t * profile b (i⁻¹ * j)) =
          ArchimedeanClass.stdPart
            (((c i * c j : ℝ) : Hyperreal) *
              Hyperreal.ofSeq fun k ↦
                Real.exp (-t * ‖b k j - b k i‖ ^ 2)) := by
      intro i j
      rw [ArchimedeanClass.stdPart_mul
        (hyperreal_coe_finite (c i * c j)) (hfin i j), stdPart_coe,
        exp_neg_mul_profile_eq hbdd halmost ht i j]
    have hsum : ∑ i ∈ F, ∑ j ∈ F,
        c i * c j * Real.exp (-t * profile b (i⁻¹ * j)) =
        ArchimedeanClass.stdPart (∑ i ∈ F, ∑ j ∈ F,
          ((c i * c j : ℝ) : Hyperreal) *
            Hyperreal.ofSeq fun k ↦
              Real.exp (-t * ‖b k j - b k i‖ ^ 2)) := by
      rw [stdPart_finset_sum F _ (fun i _ ↦
        hyperreal_finset_sum_finite F _ (fun j _ ↦
          hyperreal_mul_finite (hyperreal_coe_finite _) (hfin _ _)))]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [stdPart_finset_sum F _ (fun j _ ↦
        hyperreal_mul_finite (hyperreal_coe_finite _) (hfin _ _))]
      exact Finset.sum_congr rfl fun j _ ↦ hterm i j
    have hofseq : ∑ i ∈ F, ∑ j ∈ F,
        ((c i * c j : ℝ) : Hyperreal) *
          (Hyperreal.ofSeq fun k ↦
            Real.exp (-t * ‖b k j - b k i‖ ^ 2)) =
        Hyperreal.ofSeq fun k ↦ ∑ i ∈ F, ∑ j ∈ F,
          c i * c j * Real.exp (-t * ‖b k j - b k i‖ ^ 2) := by
      rw [show (Hyperreal.ofSeq fun k ↦ ∑ i ∈ F, ∑ j ∈ F,
          c i * c j * Real.exp (-t * ‖b k j - b k i‖ ^ 2)) =
        ofSeqRingHom (fun k ↦ ∑ i ∈ F, ∑ j ∈ F,
          c i * c j * Real.exp (-t * ‖b k j - b k i‖ ^ 2)) from rfl]
      rw [show (fun k ↦ ∑ i ∈ F, ∑ j ∈ F,
          c i * c j * Real.exp (-t * ‖b k j - b k i‖ ^ 2)) =
        ∑ i ∈ F, ∑ j ∈ F, (fun k ↦
          c i * c j * Real.exp (-t * ‖b k j - b k i‖ ^ 2)) from by
        funext k
        simp]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [show (fun k ↦
          c i * c j * Real.exp (-t * ‖b k j - b k i‖ ^ 2)) =
        (fun _ : ℕ ↦ (c i * c j : ℝ)) *
          (fun k ↦ Real.exp (-t * ‖b k j - b k i‖ ^ 2)) from by
        funext k
        simp]
      rw [map_mul]
      rfl
    rw [hsum, hofseq]
    apply ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom
    · rw [← hofseq]
      exact hyperreal_finset_sum_finite F _ (fun i _ ↦
        hyperreal_finset_sum_finite F _ (fun j _ ↦
          hyperreal_mul_finite (hyperreal_coe_finite _) (hfin _ _)))
    · rw [map_zero]
      change Hyperreal.ofSeq (fun _ : ℕ ↦ (0 : ℝ)) ≤ _
      rw [Hyperreal.ofSeq_le_ofSeq]
      exact Filter.Eventually.of_forall fun k ↦
        gaussianDisplacement_sum_nonneg F c (b k) ht

/-- **Scalar Delorme at the ultralimit.**  On a group with a Kazhdan
pair, the standard-part profile of a sequence of almost-cocycles is
uniformly bounded.  Only the limiting displacement identity `halmost` is
needed: no stage has to be a cocycle. -/
theorem profile_bounded_of_isKazhdanPair {Q : Finset G} {κ : ℝ}
    (hQ : IsKazhdanPair.{u, u} G Q κ) {b : ∀ k, G → H k}
    (hbdd : ∀ g : G, ∃ C : ℝ, ∀ k, ‖b k g‖ ^ 2 ≤ C)
    (hone : ∀ k, b k 1 = 0)
    (halmost : ∀ g h : G,
      ArchimedeanClass.stdPart
          (Hyperreal.ofSeq fun k ↦ ‖b k (g⁻¹ * h)‖ ^ 2) =
        ArchimedeanClass.stdPart
          (Hyperreal.ofSeq fun k ↦ ‖b k h - b k g‖ ^ 2)) :
    ∃ R : ℝ, ∀ g : G, profile b g ≤ R :=
  Delorme.bounded_of_gaussian_isPositiveDefinite hQ (profile b)
    (profile_one hone) (fun g ↦ profile_nonneg hbdd g)
    (fun _t ht ↦ isPositiveDefinite_exp_neg_mul_profile hbdd halmost ht.le)

omit [Group G] [∀ k, InnerProductSpace ℝ (H k)] in
/-- **Transfer**: the profile dominates the stagewise squared norms up to
any positive slack, on a hyperfilter-large set of stages. -/
theorem eventually_normSq_le_profile_add {b : ∀ k, G → H k}
    (hbdd : ∀ g : G, ∃ C : ℝ, ∀ k, ‖b k g‖ ^ 2 ≤ C) (g : G) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ k in ↑(Filter.hyperfilter ℕ),
      ‖b k g‖ ^ 2 ≤ profile b g + δ := by
  have hfin : 0 ≤ ArchimedeanClass.mk
      (Hyperreal.ofSeq fun k ↦ ‖b k g‖ ^ 2) :=
    ofSeq_norm_sq_finite (isBoundedSeq_of_normSq_le (hbdd g))
  have hlt : ArchimedeanClass.stdPart
      (Hyperreal.ofSeq fun k ↦ ‖b k g‖ ^ 2) < profile b g + δ := by
    rw [← profile_eq]
    linarith
  filter_upwards [eventually_lt_of_stdPart_lt hfin hlt] with k hk
  exact hk.le

end Profile

end UltralimitGaussian
end GroupApproximation
