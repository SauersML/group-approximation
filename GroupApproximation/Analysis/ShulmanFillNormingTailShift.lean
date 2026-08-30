import GroupApproximation.Analysis.ShulmanFillNormingTailAsymptotic

/-!
# Relabelling past the cut, instead of cornering

A tail lift controls its defects only at coordinates `n ≥ cut t`, and the
gluing of `Analysis/ShulmanFillNormingGluing` wants them controlled in the norm
of `𝒟`, which is the supremum over all coordinates.
`Analysis/ShulmanFillNormingTailTruncation` closes that gap by truncating, at
the price of the unit: the truncated family sends `1` to a projection, so the
glued map is unital into a corner rather than into the reduced product, and
`CStarAmalgamRepresentation` wants unital legs.

Cornering is avoidable, and the repository already prefers the alternative:
`Analysis/NonUnitalMFSupportCorner` does not build an abstract corner either,
it *relabels* the models so the corner becomes a full corona again.  The same
move works here and is cheaper.  Rather than zeroing the coordinates below the
cut, drop them: reindex `n ↦ n + c`.

What that buys is the whole difficulty at once.  The shifted sequence's norm is
the supremum over `n ≥ c` alone, so a tail-controlled defect becomes a
norm-controlled one; and reindexing is *unital*, since the shift of the constant
sequence of units is the constant sequence of units.  So the glued map is unital
into `∏_t 𝒟_{cut t} / ⨁_t 𝒟_{cut t}` with no corner anywhere, and the
reduced-product machinery already quantifies over a family of coordinate
algebras rather than a constant one.

The shifted data is the old data reindexed: `ι_c = fun m ↦ ι (m + c)`, and the
shifted `hone` is `hone` composed with `tendsto_add_atTop_nat c`, which is the
same one-line move `Analysis/ShulmanFillNormingEllTwoModels` makes for its
`shiftedJ`.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

universe u

section Shift

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]

/-- The models past a cut, reindexed to start at zero. -/
abbrev shiftModel (c : ℕ) : ℕ → Type u := fun m ↦ A (m + c)

/-- **Relabelling past a cut**, as a unital `*`-homomorphism of bounded
products.  Unlike truncation this preserves the unit, which is the whole
reason for preferring it. -/
def shiftSeq (c : ℕ) : StarStrong.BoundedStarSequence A →⋆ₐ[ℂ]
    StarStrong.BoundedStarSequence (shiftModel (A := A) c) where
  toFun x := ⟨fun m ↦ x (m + c), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨m, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero x (m + c)⟩⟩
  map_one' := by
    refine lp.ext (funext fun m ↦ ?_)
    rfl
  map_mul' x y := by
    refine lp.ext (funext fun m ↦ ?_)
    rfl
  map_zero' := by
    refine lp.ext (funext fun m ↦ ?_)
    rfl
  map_add' x y := by
    refine lp.ext (funext fun m ↦ ?_)
    rfl
  commutes' z := by
    refine lp.ext (funext fun m ↦ ?_)
    rfl
  map_star' x := by
    refine lp.ext (funext fun m ↦ ?_)
    rfl

@[simp] theorem shiftSeq_coord (c : ℕ) (x : StarStrong.BoundedStarSequence A)
    (m : ℕ) : (shiftSeq (A := A) c x) m = x (m + c) := rfl

/-- **The shifted norm is the supremum past the cut.**  A bound holding at every
coordinate past `c` bounds the whole shifted sequence, which is exactly what the
tail condition supplies and the sup norm of the unshifted sequence does not. -/
theorem norm_shiftSeq_le (c : ℕ) (x : StarStrong.BoundedStarSequence A)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ n, c ≤ n → ‖x n‖ ≤ C) :
    ‖shiftSeq (A := A) c x‖ ≤ C := by
  refine lp.norm_le_of_forall_le hC fun m ↦ ?_
  rw [shiftSeq_coord]
  exact h (m + c) (Nat.le_add_left c m)

/-- **The bridge.**  A family controlled past its own cut is norm-null once
relabelled there.  This is `tendsto_norm_truncSeq_of_tailNull` with the unit
kept. -/
theorem tendsto_norm_shiftSeq_of_tailNull {cut : ℕ → ℕ}
    {X : ℕ → StarStrong.BoundedStarSequence A} (h : TailNull cut X) :
    Tendsto (fun t ↦ ‖shiftSeq (A := A) (cut t) (X t)‖) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨T, hT⟩ := eventually_atTop.mp (h (ε / 2) (by linarith))
  refine ⟨T, fun t ht ↦ ?_⟩
  have hbound : ‖shiftSeq (A := A) (cut t) (X t)‖ ≤ ε / 2 :=
    norm_shiftSeq_le (cut t) (X t) (by linarith) (hT t ht)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
variable (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))

/-- The embeddings of the shifted models. -/
abbrev shiftIota (c : ℕ) :
    ∀ m, (shiftModel (A := A) c) m →⋆ₙₐ[ℂ] (H →L[ℂ] H) := fun m ↦ ι (m + c)

include hnorm in
omit [∀ n, Nontrivial (A n)] in
/-- The shifted embeddings are still contractive. -/
theorem shiftIota_norm_le (c : ℕ) :
    ∀ (m : ℕ) (x : (shiftModel (A := A) c) m), ‖shiftIota ι c m x‖ ≤ ‖x‖ :=
  fun m x ↦ hnorm (m + c) x

include hone in
omit [∀ n, Nontrivial (A n)] in
/-- **The shifted units still converge.**  This is `hone` read along `n ↦ n + c`,
the same move `shiftedJ` makes in `Analysis/ShulmanFillNormingEllTwoModels`. -/
theorem shiftIota_hone (c : ℕ) :
    ∀ v : H, Tendsto
      (fun m ↦ shiftIota ι c m (1 : (shiftModel (A := A) c) m) v) atTop (𝓝 v) :=
  fun v ↦ (hone v).comp (tendsto_add_atTop_nat c)

end Shift

end

end ShulmanFill
end GroupApproximation
