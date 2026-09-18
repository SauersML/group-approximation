import GroupApproximation.Analysis.AmenableTraceHyperlinear

/-!
Fork (lane A2Kirchberg) of the never-wired `GroupApproximation/Analysis/KirchbergTraceModels.lean`,
for Kirchberg, Math. Ann. 299 (1994), Theorem 1.1 (property (T) and the factorization property
imply residual finiteness), the Kirchberg--Thom step of table row A2 of
`simple_kazhdan_sofic_group.tex` (l.54--60; bibitem l.864--866).

# Matrix models of an amenable canonical trace, for Kirchberg's theorem

`HasFactorizationProperty G` gives unital completely positive matrix models
`φₙ` of the canonical trace of `C⋆(G)`.  Their values `Xₙ(g) = φₙ(u_g)` at the
canonical generators form a positive definite matrix function on `G`, with
`Xₙ(1) = 1` and `Xₙ(g⁻¹) = Xₙ(g)ᴴ`.  At one index `n`, for a finite set `Q`
and one element `h ≠ 1`:

* `Re tr (Xₙ(q)ᴴ Xₙ(q)) / k` is within `δ` of `1` for `q ∈ Q`, from the
  Hilbert–Schmidt multiplicativity of the models;
* `Re tr (Xₙ(h)) / k` is within `δ` of `0`, as the canonical trace vanishes
  at `u_h`.

These are the inputs of the dilation and tensor-square steps of Kirchberg's
Theorem 1.1.
-/

namespace GroupApproximation.Full.A2Kirchberg.TraceModels

open Filter Matrix Quasidiagonal AmenableTraceHyperlinear
open scoped ComplexConjugate

universe u

variable {G : Type u} [Group G]
variable (M : Quasidiagonal.AmenableTraceModel
  (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a))

/-- The model at the unit is the identity. -/
theorem modelMatrix_one (n : ℕ) : modelMatrix M n 1 = 1 := by
  rw [modelMatrix, maximalGroupCStarGenerator_one, M.map_one]

/-- **The models form a positive definite matrix function.** -/
theorem modelMatrix_kernel_nonneg (n : ℕ) (m : ℕ) (g : Fin m → G)
    (w : Fin m → M.space n → ℂ) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m, ∑ x : M.space n, ∑ y : M.space n,
      conj (w i x) * modelMatrix M n ((g i)⁻¹ * g j) x y * w j y).re := by
  have h := (M.completelyPositive n m (fun i ↦ maximalGroupCStarGenerator G (g i)) w).2
  simpa only [star_maximalGroupCStarGenerator, maximalGroupCStarGenerator_mul, modelMatrix]
    using h

/-- **One index with the estimates of Kirchberg's theorem.** -/
theorem exists_index (Q : Finset G) {h : G} (hh : h ≠ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < Fintype.card (M.space n) ∧
      (∀ q ∈ Q, |(normTrace (M.space n)
          ((modelMatrix M n q)ᴴ * modelMatrix M n q)).re - 1| < δ) ∧
      |(normTrace (M.space n) (modelMatrix M n h)).re| < δ := by
  have hcard := eventually_card_pos M
  have hgram : ∀ᶠ n in atTop, ∀ q ∈ Q, hsNorm (M.space n)
      ((modelMatrix M n q)ᴴ * modelMatrix M n q - 1) < δ := by
    rw [Filter.eventually_all_finset]
    intro q _
    exact (tendsto_hsNorm_gram M q).eventually_lt_const hδ
  have htrace := (M.tendsto_trace (maximalGroupCStarGenerator G h)).eventually_lt_const hδ
  obtain ⟨n, hn1, hn2, hn3⟩ := (hcard.and (hgram.and htrace)).exists
  refine ⟨n, hn1, fun q hq ↦ ?_, ?_⟩
  · have hone : normTrace (M.space n) (1 : Matrix (M.space n) (M.space n) ℂ) = 1 := by
      rw [normTrace, Matrix.trace_one]
      exact div_self (Nat.cast_ne_zero.mpr hn1.ne')
    calc |(normTrace (M.space n) ((modelMatrix M n q)ᴴ * modelMatrix M n q)).re - 1|
        = |(normTrace (M.space n) ((modelMatrix M n q)ᴴ * modelMatrix M n q - 1)).re| := by
          rw [normTrace_sub, hone, Complex.sub_re, Complex.one_re]
      _ ≤ ‖normTrace (M.space n) ((modelMatrix M n q)ᴴ * modelMatrix M n q - 1)‖ :=
          Complex.abs_re_le_norm _
      _ ≤ hsNorm (M.space n) ((modelMatrix M n q)ᴴ * modelMatrix M n q - 1) :=
          norm_normTrace_le_hsNorm _ _
      _ < δ := hn2 q hq
  · have hτ := canonicalMaximalTrace_generator_of_ne_one G hh
    have h3 : ‖normTrace (M.space n) (modelMatrix M n h)‖ < δ := by
      simpa [modelMatrix, hτ] using hn3
    exact (Complex.abs_re_le_norm _).trans_lt h3

end GroupApproximation.Full.A2Kirchberg.TraceModels
