import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.StdOperatorAlgebraNorm
import GroupApproximation.Analysis.CStarCompletionCoe
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Polynomial norm bounds for self-adjoint operators on `H_J`

Lane `TWWSch3c2B`, work order `WO-TWWSch-3c2-B`, spectral part. Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), the step
"`d⋆d = 0 ⇒ d = 0` in the corona `Q(J ⊗ 𝒦)`" of the absorption argument. Sources:
G. K. Pedersen, *C⋆-algebras and their automorphism groups*, 1.4.x;
E. C. Lance, *Hilbert C⋆-modules*, Ch. 2.

For a self-adjoint `a` in a C⋆-algebra and a polynomial `p` with `p(a)` self-adjoint,
`‖p(a)‖ = r(p(a)) = max |p(σ(a))| ≤ sup_{|t| ≤ ‖a‖} |p(t)|` (spectral mapping and
`r = ‖·‖` on self-adjoints). We use it for `p = X(1 - X²)ⁿ` and `p = (1 - X²)ⁿ`.

`StdBdd J` carries the C⋆-norm of `StdOperatorAlgebraNorm` but is not known here to be complete,
so the bounds are proved in the completion (a C⋆-algebra by `CStarCompletion`) and pulled back
along the isometric `⋆`-homomorphism `CStarCompletion.coeStarAlgHom`:

* `norm_aeval_le_of_isSelfAdjoint`: the generic bound;
* `StdBdd.norm_mul_one_sub_sq_pow_le`, `StdBdd.norm_one_sub_sq_pow_le`: the two bounds on `H_J`;
* `abs_mul_one_sub_sq_pow_le`, `exists_pow_one_sub_sq_le`: the scalar estimates.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule Polynomial

noncomputable section

section Generic

variable {A : Type*} [CStarAlgebra A]

/-- **Norm of a polynomial in a self-adjoint element** (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`; Pedersen 1.4). If `a` and `p(a)` are self-adjoint and
`|p(t)| ≤ c` for real `|t| ≤ ‖a‖`, then `‖p(a)‖ ≤ c`. -/
theorem norm_aeval_le_of_isSelfAdjoint {a : A} (ha : IsSelfAdjoint a) (p : ℂ[X])
    (hp : IsSelfAdjoint (aeval a p)) {c : ℝ}
    (hc : ∀ t : ℝ, |t| ≤ ‖a‖ → ‖eval (t : ℂ) p‖ ≤ c) : ‖aeval a p‖ ≤ c := by
  have hc0 : 0 ≤ c :=
    (norm_nonneg _).trans (hc 0 (by rw [abs_zero]; exact norm_nonneg a))
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (aeval a p) 0, norm_zero]
    exact hc0
  · obtain ⟨z, hz, hzn⟩ := spectrum.exists_nnnorm_eq_spectralRadius (aeval a p)
    rw [hp.spectralRadius_eq_nnnorm, ENNReal.coe_inj] at hzn
    rw [spectrum.map_polynomial_aeval] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, w = (t : ℂ) := ⟨w.re, ha.mem_spectrum_eq_re hw⟩
    have hle : |t| ≤ ‖a‖ := by
      have h := spectrum.norm_le_norm_of_mem hw
      rwa [Complex.norm_real, Real.norm_eq_abs] at h
    have hn : ‖aeval a p‖ = ‖eval (t : ℂ) p‖ := (congrArg NNReal.toReal hzn).symm
    rw [hn]
    exact hc t hle

/-- `‖a(1 - a²)ⁿ‖ ≤ sup_{|t| ≤ ‖a‖} |t(1 - t²)ⁿ|` for self-adjoint `a` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem norm_mul_one_sub_sq_pow_le_of_isSelfAdjoint {a : A} (ha : IsSelfAdjoint a) (n : ℕ)
    {c : ℝ} (hc : ∀ t : ℝ, |t| ≤ ‖a‖ → |t * (1 - t ^ 2) ^ n| ≤ c) : ‖a * (1 - a ^ 2) ^ n‖ ≤ c := by
  have hu : IsSelfAdjoint ((1 - a ^ 2) ^ n) := ((IsSelfAdjoint.one A).sub (ha.pow 2)).pow n
  have hcomm : Commute a ((1 - a ^ 2) ^ n) :=
    ((Commute.one_right a).sub_right ((Commute.refl a).pow_right 2)).pow_right n
  have hsa : IsSelfAdjoint (a * (1 - a ^ 2) ^ n) := by
    rw [isSelfAdjoint_iff, star_mul, hu.star_eq, ha.star_eq]
    exact hcomm.eq.symm
  have hy : aeval a (X * (1 - X ^ 2) ^ n : ℂ[X]) = a * (1 - a ^ 2) ^ n := by
    simp only [map_mul, map_pow, map_sub, map_one, Polynomial.aeval_X]
  rw [← hy]
  refine norm_aeval_le_of_isSelfAdjoint ha _ (by rw [hy]; exact hsa) fun t ht => ?_
  have hev : eval (t : ℂ) (X * (1 - X ^ 2) ^ n : ℂ[X]) = ((t * (1 - t ^ 2) ^ n : ℝ) : ℂ) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_one, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub,
      Complex.ofReal_one]
  rw [hev, Complex.norm_real, Real.norm_eq_abs]
  exact hc t ht

/-- `‖(1 - a²)ⁿ‖ ≤ sup_{|t| ≤ ‖a‖} |(1 - t²)ⁿ|` for self-adjoint `a` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem norm_one_sub_sq_pow_le_of_isSelfAdjoint {a : A} (ha : IsSelfAdjoint a) (n : ℕ)
    {c : ℝ} (hc : ∀ t : ℝ, |t| ≤ ‖a‖ → |(1 - t ^ 2) ^ n| ≤ c) : ‖(1 - a ^ 2) ^ n‖ ≤ c := by
  have hu : IsSelfAdjoint ((1 - a ^ 2) ^ n) := ((IsSelfAdjoint.one A).sub (ha.pow 2)).pow n
  have hy : aeval a ((1 - X ^ 2) ^ n : ℂ[X]) = (1 - a ^ 2) ^ n := by
    simp only [map_pow, map_sub, map_one, Polynomial.aeval_X]
  rw [← hy]
  refine norm_aeval_le_of_isSelfAdjoint ha _ (by rw [hy]; exact hu) fun t ht => ?_
  have hev : eval (t : ℂ) ((1 - X ^ 2) ^ n : ℂ[X]) = (((1 - t ^ 2) ^ n : ℝ) : ℂ) := by
    simp only [Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_one, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
  rw [hev, Complex.norm_real, Real.norm_eq_abs]
  exact hc t ht

end Generic

section Std

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- The bound `‖x(1 - x²)ⁿ‖ ≤ c` on `𝓑(H_J)`, through the completion (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem StdBdd.norm_mul_one_sub_sq_pow_le {x : StdBdd J} (hx : IsSelfAdjoint x) (n : ℕ)
    {c : ℝ} (hc : ∀ t : ℝ, |t| ≤ ‖x‖ → |t * (1 - t ^ 2) ^ n| ≤ c) :
    ‖x * (1 - x ^ 2) ^ n‖ ≤ c := by
  have hι : CStarCompletion.coeStarAlgHom (StdBdd J) (x * (1 - x ^ 2) ^ n) =
      CStarCompletion.coeStarAlgHom (StdBdd J) x *
        (1 - CStarCompletion.coeStarAlgHom (StdBdd J) x ^ 2) ^ n := by
    rw [map_mul, map_pow, map_sub, map_one, map_pow]
  calc ‖x * (1 - x ^ 2) ^ n‖
      = ‖CStarCompletion.coeStarAlgHom (StdBdd J) (x * (1 - x ^ 2) ^ n)‖ :=
        (CStarCompletion.norm_coeStarAlgHom _ _).symm
    _ = ‖CStarCompletion.coeStarAlgHom (StdBdd J) x *
          (1 - CStarCompletion.coeStarAlgHom (StdBdd J) x ^ 2) ^ n‖ := by rw [hι]
    _ ≤ c := norm_mul_one_sub_sq_pow_le_of_isSelfAdjoint
        (hx.map (CStarCompletion.coeStarAlgHom (StdBdd J))) n
        fun t ht => hc t (ht.trans_eq (CStarCompletion.norm_coeStarAlgHom _ x))

/-- The bound `‖(1 - x²)ⁿ‖ ≤ c` on `𝓑(H_J)`, through the completion (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem StdBdd.norm_one_sub_sq_pow_le {x : StdBdd J} (hx : IsSelfAdjoint x) (n : ℕ)
    {c : ℝ} (hc : ∀ t : ℝ, |t| ≤ ‖x‖ → |(1 - t ^ 2) ^ n| ≤ c) :
    ‖(1 - x ^ 2) ^ n‖ ≤ c := by
  have hι : CStarCompletion.coeStarAlgHom (StdBdd J) ((1 - x ^ 2) ^ n) =
      (1 - CStarCompletion.coeStarAlgHom (StdBdd J) x ^ 2) ^ n := by
    rw [map_pow, map_sub, map_one, map_pow]
  calc ‖(1 - x ^ 2) ^ n‖
      = ‖CStarCompletion.coeStarAlgHom (StdBdd J) ((1 - x ^ 2) ^ n)‖ :=
        (CStarCompletion.norm_coeStarAlgHom _ _).symm
    _ = ‖(1 - CStarCompletion.coeStarAlgHom (StdBdd J) x ^ 2) ^ n‖ := by rw [hι]
    _ ≤ c := norm_one_sub_sq_pow_le_of_isSelfAdjoint
        (hx.map (CStarCompletion.coeStarAlgHom (StdBdd J))) n
        fun t ht => hc t (ht.trans_eq (CStarCompletion.norm_coeStarAlgHom _ x))

end Std

/-! ## Scalar estimates -/

/-- `|(1 - t²)ⁿ| ≤ 1` for `|t| ≤ 1` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem abs_one_sub_sq_pow_le_one {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) : |(1 - t ^ 2) ^ n| ≤ 1 := by
  have ht2 : t ^ 2 ≤ 1 := by
    calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      _ ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
  have h0 : 0 ≤ 1 - t ^ 2 := sub_nonneg.mpr ht2
  rw [abs_of_nonneg (pow_nonneg h0 n)]
  exact pow_le_one₀ h0 (by linarith [sq_nonneg t])

/-- `|t(1 - t²)ⁿ| ≤ δ` for `|t| ≤ 1` once `(1 - δ²)ⁿ ≤ δ` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). For `|t| ≤ δ` use `|(1 - t²)ⁿ| ≤ 1`; for `|t| > δ` use
`0 ≤ 1 - t² ≤ 1 - δ²`. -/
theorem abs_mul_one_sub_sq_pow_le {δ t : ℝ} {n : ℕ} (hδ : 0 < δ) (hn : (1 - δ ^ 2) ^ n ≤ δ)
    (ht : |t| ≤ 1) : |t * (1 - t ^ 2) ^ n| ≤ δ := by
  have ht2 : t ^ 2 ≤ 1 := by
    calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      _ ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
  have h0 : 0 ≤ 1 - t ^ 2 := sub_nonneg.mpr ht2
  have hp0 : 0 ≤ (1 - t ^ 2) ^ n := pow_nonneg h0 n
  rw [abs_mul, abs_of_nonneg hp0]
  rcases le_or_gt |t| δ with h | h
  · calc |t| * (1 - t ^ 2) ^ n ≤ δ * 1 :=
          mul_le_mul h (pow_le_one₀ h0 (by linarith [sq_nonneg t])) hp0 hδ.le
      _ = δ := mul_one δ
  · have hsq : δ ^ 2 ≤ t ^ 2 := by
      calc δ ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ hδ.le h.le 2
        _ = t ^ 2 := sq_abs t
    calc |t| * (1 - t ^ 2) ^ n ≤ 1 * (1 - δ ^ 2) ^ n :=
          mul_le_mul ht (pow_le_pow_left₀ h0 (by linarith) n) hp0 zero_le_one
      _ ≤ δ := by
        rw [one_mul]
        exact hn

/-- For `δ > 0` some power `(1 - δ²)ⁿ` is at most `δ` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem exists_pow_one_sub_sq_le {δ : ℝ} (hδ : 0 < δ) : ∃ n : ℕ, (1 - δ ^ 2) ^ n ≤ δ := by
  have h1 : 1 - δ ^ 2 < 1 := by
    have h2 := pow_pos hδ 2
    linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ h1
  exact ⟨n, hn.le⟩

end

end GroupApproximation.Full.TWWSchafhauser
