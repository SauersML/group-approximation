import GroupApproximation.Analysis.ShulmanFillNormingAsymptoticMF
import GroupApproximation.Analysis.ShulmanFillNormingTailAsymptotic

/-!
# Theorem 4's other direction, in the repaired vocabulary

`StarStrongAsymptoticLift.isMFAlgebra_of_asymptoticLift` proves that a source
carrying a discrete asymptotic homomorphism into `𝒟` with faithful `*`-strong
limit is MF.  Its hypothesis is the vocabulary
`Analysis/ShulmanFillNormingPrintedPairCharacter` refutes at the printed models,
so this module re-proves the same conclusion from `StarStrongTailLift`, whose
defects are controlled only past a moving cut and whose lift clause is the
paper's pointwise one.

The shape of the argument is the shape of the old one.  Two things change.

* **The selection picks a member as well as a coordinate.**  With the exact lift
  clause, every `φ_t` was isometric, so any `t` would norm the source; with the
  pointwise clause only late `t` do, and the accuracy demanded at stage `m`
  grows with `m`.  So the diagonal runs along `m ↦ (tsel m, nsel m)` with
  `tsel m ≥ m`, and the diagonal sequence is `m ↦ φ_{tsel m} b (nsel m)`.
* **The coordinate is chosen past the cut.**  `nsel m ≥ cut (tsel m)`, which is
  what `TailNull.tendsto_diag` needs to turn each tail-controlled defect into a
  defect vanishing along the diagonal --- the hypothesis
  `quotient_diag_eq_of_tendsto` already consumed.

Everything else, including the `ε/3` argument for faithfulness, is the old proof
with `φ.toFun m` replaced by `φ.toFun (tsel m)` and one full-norm bound replaced
by its coordinate.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology PolarLiftingGeneralCStar

noncomputable section

universe u v

section Setting

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
variable {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
variable {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
variable {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
variable {B : Type v} [CStarAlgebra B]
variable {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

namespace StarStrongTailLift

/-! ## The norm in the limit -/

/-- The `*`-strong limits of a tail lift converge to the representation. -/
theorem tendsto_limit (φ : StarStrongTailLift ι hnorm hone π) (b : B) :
    Tendsto (fun t ↦ StarStrong.starStrongLimitHom ι hnorm hone
      ⟨φ.toFun t b, φ.mem t b⟩) atTop (𝓝 (π b)) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr (φ.tendsto_lift b)

/-- **The limits recover the norm.**  `π` is isometric because it is an
injective `*`-homomorphism of C-star algebras. -/
theorem tendsto_norm_limit (φ : StarStrongTailLift ι hnorm hone π)
    (hπ : Function.Injective π) (b : B) :
    Tendsto (fun t ↦ ‖StarStrong.starStrongLimitHom ι hnorm hone
      ⟨φ.toFun t b, φ.mem t b⟩‖) atTop (𝓝 ‖b‖) := by
  have hiso : Isometry π :=
    NonUnitalStarAlgHom.isometry π.toNonUnitalStarAlgHom hπ
  have hπnorm : ‖π b‖ = ‖b‖ := hiso.norm_map_of_map_zero (map_zero _) b
  have h := (φ.tendsto_limit b).norm
  rwa [hπnorm] at h

/-! ## The coordinate selection -/

/-- **Late members keep almost the whole norm at late coordinates.**  Only late
members: with the pointwise lift clause, an early `φ_t` need not be isometric. -/
theorem eventually_eventually_norm_coord_gt
    (φ : StarStrongTailLift ι hnorm hone π) (hπ : Function.Injective π)
    (b : B) {c : ℝ} (hc : 0 ≤ c) (hcb : c < ‖b‖) :
    ∀ᶠ t in atTop, ∀ᶠ n in atTop, c < ‖φ.toFun t b n‖ := by
  refine ((φ.tendsto_norm_limit hπ b).eventually_const_lt hcb).mono fun t ht ↦ ?_
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∃ᶠ n in atTop, ‖φ.toFun t b n‖ ≤ c :=
    hcon.mono fun _ hn ↦ not_lt.mp hn
  have hle : ‖StarStrong.starStrongLimit ι hnorm hone
      ⟨φ.toFun t b, φ.mem t b⟩‖ ≤ c :=
    StarStrong.norm_starStrongLimit_le_of_frequently ι hnorm hone
      ⟨φ.toFun t b, φ.mem t b⟩ hc hfreq
  exact absurd ht (not_lt.mpr hle)

/-- The same with the degenerate case absorbed. -/
theorem eventually_eventually_norm_coord_gt_sub
    (φ : StarStrongTailLift ι hnorm hone π) (hπ : Function.Injective π)
    (b : B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ᶠ n in atTop, ‖b‖ - ε < ‖φ.toFun t b n‖ := by
  rcases lt_or_ge (‖b‖ - ε) 0 with h | h
  · exact Eventually.of_forall fun _ ↦ Eventually.of_forall fun _ ↦
      lt_of_lt_of_le h (norm_nonneg _)
  · exact φ.eventually_eventually_norm_coord_gt hπ b h (by linarith)

/-- The same, uniformly over an initial segment of a sequence. -/
theorem eventually_eventually_forall_le
    (φ : StarStrongTailLift ι hnorm hone π) (hπ : Function.Injective π)
    (a : ℕ → B) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ᶠ n in atTop,
      ∀ k ≤ m, ‖a k‖ - ε < ‖φ.toFun t (a k) n‖ := by
  induction m with
  | zero =>
    refine (φ.eventually_eventually_norm_coord_gt_sub hπ (a 0) hε).mono ?_
    intro t ht
    refine ht.mono fun n hn k hk ↦ ?_
    rw [Nat.le_zero.mp hk]
    exact hn
  | succ m ih =>
    refine (ih.and (φ.eventually_eventually_norm_coord_gt_sub hπ (a (m + 1)) hε)).mono ?_
    rintro t ⟨ht1, ht2⟩
    refine (ht1.and ht2).mono fun n hn k hk ↦ ?_
    rcases eq_or_lt_of_le hk with h | h
    · rw [h]
      exact hn.2
    · exact hn.1 k (Nat.lt_succ_iff.mp h)

/-- **The diagonal choice.**  At stage `m` it produces a member `tsel m ≥ m` and
a coordinate `nsel m ≥ cut (tsel m)` at which that member norms the first `m`
entries of `a` to within `1/(m+1)`. -/
theorem exists_diagonal_selection (φ : StarStrongTailLift ι hnorm hone π)
    (hπ : Function.Injective π) (a : ℕ → B) :
    ∃ tsel nsel : ℕ → ℕ, (∀ m, m ≤ tsel m) ∧ (∀ m, φ.cut (tsel m) ≤ nsel m) ∧
      ∀ m, ∀ k ≤ m,
        ‖a k‖ - 1 / (m + 1 : ℝ) < ‖φ.toFun (tsel m) (a k) (nsel m)‖ := by
  have hstage : ∀ m : ℕ, ∃ t, m ≤ t ∧ ∃ n, φ.cut t ≤ n ∧
      ∀ k ≤ m, ‖a k‖ - 1 / (m + 1 : ℝ) < ‖φ.toFun t (a k) n‖ := by
    intro m
    obtain ⟨t, htail, hm⟩ :=
      (((φ.eventually_eventually_forall_le hπ a m
        (by positivity : (0 : ℝ) < 1 / (m + 1 : ℝ))).and
          (eventually_ge_atTop m))).exists
    obtain ⟨n, hn, hcut⟩ := (htail.and (eventually_ge_atTop (φ.cut t))).exists
    exact ⟨t, hm, n, hcut, hn⟩
  choose tsel htsel nsel hcut hnorm using hstage
  exact ⟨tsel, nsel, htsel, hcut, hnorm⟩

/-- Every map of the family kills zero. -/
theorem toFun_zero (φ : StarStrongTailLift ι hnorm hone π) (t : ℕ) :
    φ.toFun t (0 : B) = 0 := by
  have h : ‖φ.toFun t (0 : B)‖ ≤ ‖(0 : B)‖ := φ.norm_le t 0
  rw [norm_zero] at h
  exact norm_le_zero_iff.mp h

/-- Each coordinate of each member is contractive. -/
theorem norm_coord_le (φ : StarStrongTailLift ι hnorm hone π)
    (t : ℕ) (b : B) (n : ℕ) : ‖φ.toFun t b n‖ ≤ ‖b‖ :=
  (lp.norm_apply_le_norm ENNReal.top_ne_zero (φ.toFun t b) n).trans (φ.norm_le t b)

end StarStrongTailLift

/-! ## The diagonal sequence and its reduced-product class -/

section Diagonal

variable (φ : StarStrongTailLift ι hnorm hone π) (tsel nsel : ℕ → ℕ)

namespace StarStrongTailLift

/-- The diagonal sequence `m ↦ (φ_{tsel m} b) (nsel m)`, bounded by `‖b‖`. -/
def diagSeq (b : B) : BoundedCStarSequence (fun m ↦ A (nsel m)) :=
  ⟨fun m ↦ φ.toFun (tsel m) b (nsel m), memℓp_infty ⟨‖b‖, by
    rintro _ ⟨m, rfl⟩
    exact φ.norm_coord_le (tsel m) b (nsel m)⟩⟩

@[simp] theorem diagSeq_apply (b : B) (m : ℕ) :
    diagSeq φ tsel nsel b m = φ.toFun (tsel m) b (nsel m) := rfl

/-- **The transfer lemma for every defect**, in the repaired vocabulary: a
defect controlled past the cut and read along a selection past the cut agrees in
the reduced product. -/
theorem quotient_diag_eq_of_tailNull
    (htsel : ∀ m, m ≤ tsel m) (hcut : ∀ m, φ.cut (tsel m) ≤ nsel m)
    (u v : ℕ → StarStrong.BoundedStarSequence A)
    (x y : BoundedCStarSequence (fun m ↦ A (nsel m)))
    (hx : ∀ m, x m = u (tsel m) (nsel m)) (hy : ∀ m, y m = v (tsel m) (nsel m))
    (h : TailNull φ.cut (fun t ↦ u t - v t)) :
    cStarProductCoronaQuotient (fun m ↦ A (nsel m)) cofinite x =
      cStarProductCoronaQuotient (fun m ↦ A (nsel m)) cofinite y := by
  refine cStarProductCoronaQuotient_eq_of_tendsto_norm_sub x y ?_
  have hdiag := h.tendsto_diag (tsel := tsel) (nsel := nsel)
    (tendsto_atTop_mono htsel tendsto_id) hcut
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun m ↦ ?_) hdiag
  rw [hx m, hy m]
  exact le_of_eq rfl

/-- **The diagonal class is a `*`-homomorphism.** -/
def diagHom (htsel : ∀ m, m ≤ tsel m) (hcut : ∀ m, φ.cut (tsel m) ≤ nsel m) :
    B →⋆ₙₐ[ℂ] CStarProductCorona (fun m ↦ A (nsel m)) cofinite where
  toFun b := cStarProductCoronaQuotient (fun m ↦ A (nsel m)) cofinite
    (diagSeq φ tsel nsel b)
  map_zero' := by
    have hz : TailNull φ.cut
        (fun t ↦ φ.toFun t (0 : B) - (0 : StarStrong.BoundedStarSequence A)) := by
      intro ε hε
      refine Eventually.of_forall fun t ↦ ?_
      intro n _hn
      beta_reduce
      rw [toFun_zero φ t, sub_zero]
      simpa using hε.le
    have hmain := quotient_diag_eq_of_tailNull φ tsel nsel htsel hcut
      (fun t ↦ φ.toFun t 0) (fun _ ↦ 0) (diagSeq φ tsel nsel 0) 0
      (fun _ ↦ rfl) (fun _ ↦ rfl) hz
    rw [map_zero] at hmain
    exact hmain
  map_add' b c := by
    rw [← map_add]
    exact quotient_diag_eq_of_tailNull φ tsel nsel htsel hcut
      (fun t ↦ φ.toFun t (b + c)) (fun t ↦ φ.toFun t b + φ.toFun t c) _ _
      (fun _ ↦ rfl) (fun _ ↦ rfl)
      ((φ.tail_add b c).mono fun t n ↦ by
        rw [show φ.toFun t (b + c) - (φ.toFun t b + φ.toFun t c)
          = φ.toFun t (b + c) - φ.toFun t b - φ.toFun t c from by abel])
  map_mul' b c := by
    rw [← map_mul]
    exact quotient_diag_eq_of_tailNull φ tsel nsel htsel hcut
      (fun t ↦ φ.toFun t (b * c)) (fun t ↦ φ.toFun t b * φ.toFun t c) _ _
      (fun _ ↦ rfl) (fun _ ↦ rfl) (φ.tail_mul b c)
  map_smul' z b := by
    rw [← map_smul]
    exact quotient_diag_eq_of_tailNull φ tsel nsel htsel hcut
      (fun t ↦ φ.toFun t (z • b)) (fun t ↦ z • φ.toFun t b) _ _
      (fun _ ↦ rfl) (fun _ ↦ rfl) (φ.tail_smul z b)
  map_star' b := by
    rw [← map_star]
    exact quotient_diag_eq_of_tailNull φ tsel nsel htsel hcut
      (fun t ↦ φ.toFun t (star b)) (fun t ↦ star (φ.toFun t b)) _ _
      (fun _ ↦ rfl) (fun _ ↦ rfl) (φ.tail_star b)

@[simp] theorem diagHom_apply (htsel : ∀ m, m ≤ tsel m)
    (hcut : ∀ m, φ.cut (tsel m) ≤ nsel m) (b : B) :
    diagHom φ tsel nsel htsel hcut b =
      cStarProductCoronaQuotient (fun m ↦ A (nsel m)) cofinite
        (diagSeq φ tsel nsel b) := rfl

/-! ## Faithfulness -/

/-- **The diagonal homomorphism is faithful.**  The `ε/3` argument of
`Analysis/ShulmanFillNormingAsymptoticMF`, with the additivity defect read at
the selected coordinate instead of in the sup norm: a nonzero `z` within
`‖z‖/8` of some `a k` inherits from `a k` a coordinate norm above `‖z‖/2` at
every late stage, and a class with such coordinates is not zero. -/
theorem diagHom_injective (htsel : ∀ m, m ≤ tsel m)
    (hcut : ∀ m, φ.cut (tsel m) ≤ nsel m) (a : ℕ → B) (ha : DenseRange a)
    (hsel : ∀ m, ∀ k ≤ m,
      ‖a k‖ - 1 / (m + 1 : ℝ) < ‖φ.toFun (tsel m) (a k) (nsel m)‖) :
    Function.Injective (diagHom φ tsel nsel htsel hcut) := by
  intro b c hbc
  by_contra hne
  have hz : b - c ≠ 0 := sub_ne_zero.mpr hne
  have hr : 0 < ‖b - c‖ := norm_pos_iff.mpr hz
  have h0 : diagHom φ tsel nsel htsel hcut (b - c) = 0 := by
    rw [map_sub, hbc, sub_self]
  have hnull : IsNullCStarSequence (fun m ↦ A (nsel m)) cofinite
      (diagSeq φ tsel nsel (b - c)) :=
    (cStarProductCoronaQuotient_eq_zero_iff (fun m ↦ A (nsel m)) cofinite
      (diagSeq φ tsel nsel (b - c))).mp h0
  have htend : Tendsto
      (fun m ↦ ‖φ.toFun (tsel m) (b - c) (nsel m)‖) atTop (𝓝 0) := by
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
  have hsum : b - c - a k + a k = b - c := by abel
  have hdefect : Tendsto (fun m ↦
      ‖φ.toFun (tsel m) (b - c) (nsel m)
        - φ.toFun (tsel m) (b - c - a k) (nsel m)
        - φ.toFun (tsel m) (a k) (nsel m)‖) atTop (𝓝 0) := by
    have hd := φ.tail_add (b - c - a k) (a k)
    rw [hsum] at hd
    exact hd.tendsto_diag (tendsto_atTop_mono htsel tendsto_id) hcut
  have hlow : ∀ᶠ m in atTop,
      ‖b - c‖ / 2 < ‖φ.toFun (tsel m) (b - c) (nsel m)‖ := by
    refine (((eventually_ge_atTop k).and (eventually_ge_atTop M)).and
      (hdefect (Iio_mem_nhds (by linarith : (0 : ℝ) < ‖b - c‖ / 8)))).mono ?_
    rintro m ⟨⟨hmk, hmM⟩, hmd⟩
    have h1 : ‖a k‖ - 1 / (m + 1 : ℝ) < ‖φ.toFun (tsel m) (a k) (nsel m)‖ :=
      hsel m k hmk
    have hmono : (1 : ℝ) / (m + 1) ≤ 1 / (M + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have hcast : (M : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hmM
      linarith
    have hsplit : φ.toFun (tsel m) (b - c) (nsel m)
        - φ.toFun (tsel m) (a k) (nsel m)
        = φ.toFun (tsel m) (b - c - a k) (nsel m)
          + (φ.toFun (tsel m) (b - c) (nsel m)
            - φ.toFun (tsel m) (b - c - a k) (nsel m)
            - φ.toFun (tsel m) (a k) (nsel m)) := by
      abel
    have hbound : ‖φ.toFun (tsel m) (b - c) (nsel m)
        - φ.toFun (tsel m) (a k) (nsel m)‖ ≤ ‖b - c - a k‖ + ‖b - c‖ / 8 := by
      rw [hsplit]
      exact (norm_add_le _ _).trans
        (add_le_add (φ.norm_coord_le (tsel m) (b - c - a k) (nsel m)) hmd.le)
    have hrev : ‖φ.toFun (tsel m) (a k) (nsel m)‖
        - ‖φ.toFun (tsel m) (b - c) (nsel m)‖
          ≤ ‖φ.toFun (tsel m) (a k) (nsel m)
            - φ.toFun (tsel m) (b - c) (nsel m)‖ :=
      norm_sub_norm_le _ _
    rw [norm_sub_rev] at hrev
    linarith
  have hhigh : ∀ᶠ m in atTop,
      ‖φ.toFun (tsel m) (b - c) (nsel m)‖ < ‖b - c‖ / 2 :=
    htend (Iio_mem_nhds (by linarith))
  obtain ⟨m, hm1, hm2⟩ := (hlow.and hhigh).exists
  linarith

end StarStrongTailLift

end Diagonal

/-! ## The endpoint -/

namespace StarStrongTailLift

/-- **Shulman's Theorem 4, the direction his Theorem 10 ends with, in the
repaired vocabulary.**  A separable C-star algebra carrying a discrete
asymptotic homomorphism into `𝒟` whose defects are controlled past a moving cut
and whose `*`-strong limits converge to a faithful representation is MF, as soon
as the coordinate algebras are.

This is the consumer `Analysis/ShulmanFillNormingPrintedPairCharacter` leaves
standing: it asks strictly less of its lift than
`isMFAlgebra_of_asymptoticLift` does, by `StarStrongAsymptoticLift.toTail`. -/
theorem isMFAlgebra_of_tailLift [TopologicalSpace.SeparableSpace B]
    (φ : StarStrongTailLift ι hnorm hone π)
    (hA : ∀ n, HasMFEmbedding (A n)) (hπ : Function.Injective π) :
    IsMFAlgebra B := by
  have ha : DenseRange (TopologicalSpace.denseSeq B) :=
    TopologicalSpace.denseRange_denseSeq B
  obtain ⟨tsel, nsel, htsel, hcut, hsel⟩ :=
    φ.exists_diagonal_selection hπ (TopologicalSpace.denseSeq B)
  exact ReducedProductMFPermanence.isMFAlgebra_of_injective_reducedProduct
    (fun m ↦ A (nsel m)) (diagHom φ tsel nsel htsel hcut)
    (diagHom_injective φ tsel nsel htsel hcut (TopologicalSpace.denseSeq B) ha hsel)
    (fun m ↦ hA (nsel m))

end StarStrongTailLift

end Setting

end

end ShulmanFill
end GroupApproximation
