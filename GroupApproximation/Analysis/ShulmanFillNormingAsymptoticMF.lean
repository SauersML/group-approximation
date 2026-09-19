import GroupApproximation.Analysis.ReducedProductMFPermanence
import GroupApproximation.Analysis.ShulmanFillNormingAsymptotic

/-!
# Theorem 4, the direction Theorem 10 ends with, in the right vocabulary

`StarStrong.isMFAlgebra_of_starStrongLift` proves that a `*`-homomorphic lift
into `𝒟` with faithful `*`-strong limit makes the source MF.  That statement is
true but unusable: `Analysis/ShulmanFillNormingResiduallyFinite` shows its
hypothesis forces the source to be residually finite-dimensional, so no simple
infinite-dimensional MF algebra can satisfy it.

This module proves the same conclusion from the hypothesis Shulman's Theorem 4
actually carries — a **discrete asymptotic homomorphism**
(`ShulmanFill.StarStrongAsymptoticLift`, `Analysis/ShulmanFillNormingAsymptotic`).
Its coordinates are not homomorphisms, only asymptotically multiplicative maps,
so the obstruction does not apply and the statement is usable.

## The proof

Everything rests on one inequality already in the repository,
`StarStrong.norm_starStrongLimit_le_of_frequently`: a bound met infinitely
often by the coordinates bounds the `*`-strong limit.  The limit of `φ_t b` is
`π b` and `π` is isometric, so no `c < ‖b‖` bounds the coordinates infinitely
often — *eventually every coordinate carries almost the full norm*.  That is
`StarStrongAsymptoticLift.eventually_norm_coord_gt`, and without it a single
coordinate of a sup-normed sequence would carry no information at all.

So: take a dense sequence `a` of `B`; for stage `m` choose one coordinate
`n m` at which `φ_m` still norms `a 0, …, a m` to within `1/(m+1)`, and set
`Λ_m := (φ_m ·) (n m) : B → A (n m)`.  Since the stage index `m` also runs to
infinity, every defect of `Λ_m` is dominated by the `m`-th defect of `φ` and
vanishes, so `b ↦ [m ↦ Λ_m b]` is a genuine `*`-homomorphism into the reduced
product `∏ₘ A (n m) / ⨁ₘ A (n m)`.  An `ε/3` argument off the dense sequence
makes it faithful, and `ReducedProductMFPermanence` concludes.

Which hypothesis does what: the stage index running to infinity gives
multiplicativity of the limit map, and the coordinate selection gives
faithfulness.  The selection is the only place separability is used.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology PolarLiftingGeneralCStar

noncomputable section

universe u v

/-! ## Null differences in a reduced product -/

section Quotient

variable {M : ℕ → Type u} [∀ m, CStarAlgebra (M m)] [∀ m, Nontrivial (M m)]

/-- Two bounded sequences whose coordinatewise difference is norm-null have the
same class in the reduced product. -/
theorem cStarProductCoronaQuotient_eq_of_tendsto_norm_sub
    (x y : BoundedCStarSequence M)
    (h : Tendsto (fun m ↦ ‖x m - y m‖) atTop (𝓝 0)) :
    cStarProductCoronaQuotient M cofinite x =
      cStarProductCoronaQuotient M cofinite y := by
  have hnull : IsNullCStarSequence M cofinite (x - y) := by
    rw [← Nat.cofinite_eq_atTop] at h
    exact h
  have hzero : cStarProductCoronaQuotient M cofinite (x - y) = 0 :=
    (cStarProductCoronaQuotient_eq_zero_iff M cofinite (x - y)).mpr hnull
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

end Quotient

section Setting

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
variable {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
variable {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
variable {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
variable {B : Type v} [CStarAlgebra B]
variable {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

namespace StarStrongAsymptoticLift

/-! ## The coordinate selection -/

/-- **Coordinates keep almost the whole norm, eventually.**  The degenerate
case `‖b‖ ≤ ε` is free because norms are nonnegative; otherwise this is
`eventually_norm_coord_gt`. -/
theorem eventually_norm_coord_gt_sub
    (φ : StarStrongAsymptoticLift ι hnorm hone π) (hπ : Function.Injective π)
    (t : ℕ) (b : B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ‖b‖ - ε < ‖φ.toFun t b n‖ := by
  rcases lt_or_ge (‖b‖ - ε) 0 with h | h
  · exact Eventually.of_forall fun n ↦ lt_of_lt_of_le h (norm_nonneg _)
  · exact φ.eventually_norm_coord_gt hπ t b h (by linarith)

/-- The same, uniformly over an initial segment of a sequence: finitely many
eventual conditions still hold eventually. -/
theorem eventually_forall_le_norm_coord_gt_sub
    (φ : StarStrongAsymptoticLift ι hnorm hone π) (hπ : Function.Injective π)
    (a : ℕ → B) (t m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ k ≤ m, ‖a k‖ - ε < ‖φ.toFun t (a k) n‖ := by
  induction m with
  | zero =>
    refine (φ.eventually_norm_coord_gt_sub hπ t (a 0) hε).mono ?_
    intro n hn k hk
    rw [Nat.le_zero.mp hk]
    exact hn
  | succ m ih =>
    refine (ih.and (φ.eventually_norm_coord_gt_sub hπ t (a (m + 1)) hε)).mono ?_
    intro n hn k hk
    rcases eq_or_lt_of_le hk with h | h
    · rw [h]
      exact hn.2
    · exact hn.1 k (Nat.lt_succ_iff.mp h)

/-- **The diagonal choice.**  For each stage `m` there is a coordinate at which
`φ_m` norms the first `m` members of `a` to within `1/(m+1)`. -/
theorem exists_diagonal_coordinate
    (φ : StarStrongAsymptoticLift ι hnorm hone π) (hπ : Function.Injective π)
    (a : ℕ → B) (m : ℕ) :
    ∃ N : ℕ, ∀ k ≤ m, ‖a k‖ - 1 / (m + 1 : ℝ) < ‖φ.toFun m (a k) N‖ :=
  (φ.eventually_forall_le_norm_coord_gt_sub hπ a m m
    (by positivity : (0 : ℝ) < 1 / (m + 1 : ℝ))).exists

/-- Every map of the family kills zero: it is a contraction, and `‖0‖ = 0`. -/
theorem toFun_zero (φ : StarStrongAsymptoticLift ι hnorm hone π) (m : ℕ) :
    φ.toFun m (0 : B) = 0 := by
  have h : ‖φ.toFun m (0 : B)‖ ≤ ‖(0 : B)‖ := φ.norm_le m 0
  rw [norm_zero] at h
  exact norm_le_zero_iff.mp h

end StarStrongAsymptoticLift

/-! ## The diagonal sequence and its reduced-product class -/

section Diagonal

variable (φ : StarStrongAsymptoticLift ι hnorm hone π) (nsel : ℕ → ℕ)

namespace StarStrongAsymptoticLift

/-- The diagonal sequence `m ↦ (φ_m b) (n m)`, bounded by `‖b‖`. -/
def diagSeq (b : B) : BoundedCStarSequence (fun m ↦ A (nsel m)) :=
  ⟨fun m ↦ φ.toFun m b (nsel m), memℓp_infty ⟨‖b‖, by
    rintro _ ⟨m, rfl⟩
    exact φ.norm_coord_le m b (nsel m)⟩⟩

@[simp] theorem diagSeq_apply (b : B) (m : ℕ) :
    diagSeq φ nsel b m = φ.toFun m b (nsel m) := rfl

/-- **The transfer lemma for every defect.**  If two families of bounded
sequences have vanishing difference in the product norm, then the diagonal
coordinates they cut out agree in the reduced product.  Each field of
`diagHom` is this lemma at one defect of `φ`. -/
theorem quotient_diag_eq_of_tendsto
    (u v : ℕ → StarStrong.BoundedStarSequence A)
    (x y : BoundedCStarSequence (fun m ↦ A (nsel m)))
    (hx : ∀ m, x m = u m (nsel m)) (hy : ∀ m, y m = v m (nsel m))
    (h : Tendsto (fun m ↦ ‖u m - v m‖) atTop (𝓝 0)) :
    cStarProductCoronaQuotient (fun m ↦ A (nsel m)) cofinite x =
      cStarProductCoronaQuotient (fun m ↦ A (nsel m)) cofinite y := by
  refine cStarProductCoronaQuotient_eq_of_tendsto_norm_sub x y ?_
  refine squeeze_zero (fun m ↦ norm_nonneg _) (fun m ↦ ?_) h
  rw [hx m, hy m]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero (u m - v m) (nsel m)

/-- **The diagonal class is a `*`-homomorphism.**  Every defect of `Λ_m` is
dominated by the `m`-th defect of `φ`, and the stage index runs to infinity, so
every defect vanishes in the reduced product. -/
def diagHom : B →⋆ₙₐ[ℂ] CStarProductCorona (fun m ↦ A (nsel m)) cofinite where
  toFun b := cStarProductCoronaQuotient (fun m ↦ A (nsel m)) cofinite
    (diagSeq φ nsel b)
  map_zero' := by
    have hz : Tendsto
        (fun m ↦ ‖φ.toFun m (0 : B) - (0 : StarStrong.BoundedStarSequence A)‖)
        atTop (𝓝 0) := by
      have hfun : (fun m ↦
          ‖φ.toFun m (0 : B) - (0 : StarStrong.BoundedStarSequence A)‖) =
            fun _ : ℕ ↦ (0 : ℝ) := by
        funext m
        rw [toFun_zero φ m, sub_zero, norm_zero]
      rw [hfun]
      exact tendsto_const_nhds
    have hmain : cStarProductCoronaQuotient (fun m ↦ A (nsel m)) cofinite
        (diagSeq φ nsel 0) =
      cStarProductCoronaQuotient (fun m ↦ A (nsel m)) cofinite 0 :=
      quotient_diag_eq_of_tendsto nsel (fun m ↦ φ.toFun m 0) (fun _ ↦ 0)
        (diagSeq φ nsel 0) 0 (fun _ ↦ rfl) (fun _ ↦ rfl) hz
    rw [map_zero] at hmain
    exact hmain
  map_add' b c := by
    have hz : Tendsto
        (fun m ↦ ‖φ.toFun m (b + c) - (φ.toFun m b + φ.toFun m c)‖)
        atTop (𝓝 0) := by
      simpa only [sub_add_eq_sub_sub] using φ.tendsto_add b c
    rw [← map_add]
    exact quotient_diag_eq_of_tendsto nsel (fun m ↦ φ.toFun m (b + c))
      (fun m ↦ φ.toFun m b + φ.toFun m c) _ _ (fun _ ↦ rfl) (fun _ ↦ rfl) hz
  map_mul' b c := by
    rw [← map_mul]
    exact quotient_diag_eq_of_tendsto nsel (fun m ↦ φ.toFun m (b * c))
      (fun m ↦ φ.toFun m b * φ.toFun m c) _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)
      (φ.tendsto_mul b c)
  map_smul' z b := by
    rw [← map_smul]
    exact quotient_diag_eq_of_tendsto nsel (fun m ↦ φ.toFun m (z • b))
      (fun m ↦ z • φ.toFun m b) _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)
      (φ.tendsto_smul z b)
  map_star' b := by
    rw [← map_star]
    exact quotient_diag_eq_of_tendsto nsel (fun m ↦ φ.toFun m (star b))
      (fun m ↦ star (φ.toFun m b)) _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)
      (φ.tendsto_star b)

@[simp] theorem diagHom_apply (b : B) :
    diagHom φ nsel b = cStarProductCoronaQuotient (fun m ↦ A (nsel m)) cofinite
      (diagSeq φ nsel b) := rfl

/-! ## Faithfulness -/

/-- **The diagonal homomorphism is faithful.**  Off the dense sequence an
`ε/3` argument does the work: the additivity defect makes `Λ_m` almost
additive, so a nonzero `z` within `‖z‖/8` of some `a k` inherits from `a k` a
coordinate norm above `‖z‖/2` at every late stage, and a class with such
coordinates is not the zero class. -/
theorem diagHom_injective (_hπ : Function.Injective π) (a : ℕ → B)
    (ha : DenseRange a)
    (hsel : ∀ m, ∀ k ≤ m,
      ‖a k‖ - 1 / (m + 1 : ℝ) < ‖φ.toFun m (a k) (nsel m)‖) :
    Function.Injective (diagHom φ nsel) := by
  intro b c hbc
  by_contra hne
  have hz : b - c ≠ 0 := sub_ne_zero.mpr hne
  have hr : 0 < ‖b - c‖ := norm_pos_iff.mpr hz
  have h0 : diagHom φ nsel (b - c) = 0 := by
    rw [map_sub, hbc, sub_self]
  have hnull : IsNullCStarSequence (fun m ↦ A (nsel m)) cofinite
      (diagSeq φ nsel (b - c)) :=
    (cStarProductCoronaQuotient_eq_zero_iff (fun m ↦ A (nsel m)) cofinite
      (diagSeq φ nsel (b - c))).mp h0
  have htend : Tendsto (fun m ↦ ‖φ.toFun m (b - c) (nsel m)‖) atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact hnull
  obtain ⟨k, hk⟩ : ∃ k, ‖b - c - a k‖ < ‖b - c‖ / 8 := by
    obtain ⟨k, hk⟩ :=
      Metric.denseRange_iff.mp ha (b - c) (‖b - c‖ / 8) (by linarith)
    exact ⟨k, by rwa [dist_eq_norm] at hk⟩
  have hak : ‖b - c‖ - ‖b - c - a k‖ ≤ ‖a k‖ := by
    have h := norm_sub_norm_le (b - c) (b - c - a k)
    simpa using h
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 1 / (M + 1 : ℝ) < ‖b - c‖ / 8 :=
    exists_nat_one_div_lt (by linarith)
  have hdefect : ∀ᶠ m in atTop,
      ‖φ.toFun m (b - c) - φ.toFun m (b - c - a k) - φ.toFun m (a k)‖ <
        ‖b - c‖ / 8 := by
    have heq : b - c - a k + a k = b - c := by abel
    have hd := φ.tendsto_add (b - c - a k) (a k)
    rw [heq] at hd
    exact hd (Iio_mem_nhds (by linarith))
  have hlow : ∀ᶠ m in atTop,
      ‖b - c‖ / 2 < ‖φ.toFun m (b - c) (nsel m)‖ := by
    refine (((eventually_ge_atTop k).and (eventually_ge_atTop M)).and
      hdefect).mono ?_
    rintro m ⟨⟨hmk, hmM⟩, hmd⟩
    have h1 : ‖a k‖ - 1 / (m + 1 : ℝ) < ‖φ.toFun m (a k) (nsel m)‖ :=
      hsel m k hmk
    have hmono : (1 : ℝ) / (m + 1) ≤ 1 / (M + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have hcast : (M : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hmM
      linarith
    have hdiff : φ.toFun m (b - c) - φ.toFun m (a k) =
        φ.toFun m (b - c - a k) +
          (φ.toFun m (b - c) - φ.toFun m (b - c - a k) -
            φ.toFun m (a k)) := by
      abel
    have hbound : ‖φ.toFun m (b - c) - φ.toFun m (a k)‖ ≤
        ‖b - c - a k‖ + ‖b - c‖ / 8 := by
      rw [hdiff]
      exact (norm_add_le _ _).trans
        (add_le_add (φ.norm_le m (b - c - a k)) (le_of_lt hmd))
    have hco : ‖φ.toFun m (b - c) (nsel m) - φ.toFun m (a k) (nsel m)‖ ≤
        ‖φ.toFun m (b - c) - φ.toFun m (a k)‖ :=
      lp.norm_apply_le_norm ENNReal.top_ne_zero
        (φ.toFun m (b - c) - φ.toFun m (a k)) (nsel m)
    have hrev : ‖φ.toFun m (a k) (nsel m)‖ -
        ‖φ.toFun m (b - c) (nsel m)‖ ≤
          ‖φ.toFun m (a k) (nsel m) - φ.toFun m (b - c) (nsel m)‖ :=
      norm_sub_norm_le _ _
    rw [norm_sub_rev] at hrev
    linarith
  have hhigh : ∀ᶠ m in atTop,
      ‖φ.toFun m (b - c) (nsel m)‖ < ‖b - c‖ / 2 :=
    htend (Iio_mem_nhds (by linarith))
  obtain ⟨m, hm1, hm2⟩ := (hlow.and hhigh).exists
  linarith

end StarStrongAsymptoticLift

end Diagonal

/-! ## The endpoint -/

namespace StarStrongAsymptoticLift

/-- **Shulman's Theorem 4, the direction his Theorem 10 ends with, in the
vocabulary Theorem 4 is stated in.**  A separable C-star algebra carrying a
discrete asymptotic homomorphism into `𝒟` whose `*`-strong limit is a faithful
representation is MF, as soon as the coordinate algebras are.

This replaces `StarStrong.isMFAlgebra_of_starStrongLift`, whose
`*`-homomorphic hypothesis no simple infinite-dimensional MF algebra can meet
(`Analysis/ShulmanFillNormingResiduallyFinite`). -/
theorem isMFAlgebra_of_asymptoticLift [TopologicalSpace.SeparableSpace B]
    (φ : StarStrongAsymptoticLift ι hnorm hone π)
    (hA : ∀ n, HasMFEmbedding (A n)) (hπ : Function.Injective π) :
    IsMFAlgebra B := by
  have ha : DenseRange (TopologicalSpace.denseSeq B) :=
    TopologicalSpace.denseRange_denseSeq B
  choose nsel hnsel using
    φ.exists_diagonal_coordinate hπ (TopologicalSpace.denseSeq B)
  exact ReducedProductMFPermanence.isMFAlgebra_of_injective_reducedProduct
    (fun m ↦ A (nsel m)) (diagHom φ nsel)
    (diagHom_injective φ nsel hπ (TopologicalSpace.denseSeq B) ha hnsel)
    (fun m ↦ hA (nsel m))

end StarStrongAsymptoticLift

end Setting

end

end ShulmanFill
end GroupApproximation
