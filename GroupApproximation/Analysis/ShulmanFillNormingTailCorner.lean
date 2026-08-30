import GroupApproximation.Analysis.ShulmanFillNormingTailTruncation

/-!
# The cut projection lives in `𝒟`, and truncation does not move the limit

`Analysis/ShulmanFillNormingTailTruncation` truncates a tail lift past its cut,
which is what makes its defects vanish in the norm of `𝒟` and so lets the
gluing consume them.  For that to be worth anything the truncation has to stay
inside `𝒟` and has to leave the `*`-strong limit alone; otherwise the glued map
would represent something other than the representation it started from.

Both facts come from one observation: `cutProj c` is itself an element of `𝒟`,
and its `*`-strong limit is `1`.  Its coordinates are `1` past the cut and `0`
below, so its `ι`-images agree with `ι n 1` eventually, and `hone` says those
converge `*`-strongly to `1`.  Everything else is multiplicativity of `q`:

    `q (truncSeq c x) = q (cutProj c * x) = q (cutProj c) * q x = q x` .

So truncating is invisible to the limit, and the price of it is exactly the one
recorded in `Analysis/ShulmanFillNormingTailTruncation`: the truncated family is
unital into the corner cut by these projections rather than into `𝒟` itself.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

universe u

section Corner

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
variable (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))

include hone in
/-- **The cut projection converges `*`-strongly to the identity.**  Past the cut
its coordinates are the units, and `hone` is exactly the statement that those
converge.  Both clauses of `IsStarStrongLimit` reduce to that one, because the
projection is self-adjoint at every coordinate. -/
theorem cutProj_isStarStrongLimit (c : ℕ) :
    StarStrong.IsStarStrongLimit
      (fun n ↦ ι n ((cutProj (A := A) c) n)) 1 := by
  have hev : ∀ v : H,
      Tendsto (fun n ↦ ι n ((cutProj (A := A) c) n) v) atTop (𝓝 v) := by
    intro v
    refine Tendsto.congr' ?_ (hone v)
    filter_upwards [eventually_ge_atTop c] with n hn
    rw [cutProj_apply, if_pos hn]
  have hstar : ∀ n : ℕ,
      star (ι n ((cutProj (A := A) c) n)) = ι n ((cutProj (A := A) c) n) := by
    intro n
    rw [← map_star]
    congr 1
    rw [cutProj_apply]
    by_cases h : c ≤ n <;> simp [h]
  refine ⟨fun v ↦ hev v, fun v ↦ ?_⟩
  simp only [hstar, star_one]
  exact hev v

/-- The cut projection is an element of `𝒟`. -/
theorem cutProj_mem (c : ℕ) :
    cutProj (A := A) c ∈ StarStrong.starStrongSubalgebra ι hnorm hone :=
  ⟨1, cutProj_isStarStrongLimit ι hone c⟩

/-- **The cut projection is a unit in the limit.** -/
theorem starStrongLimit_cutProj (c : ℕ) :
    StarStrong.starStrongLimit ι hnorm hone
        ⟨cutProj (A := A) c, cutProj_mem ι hnorm hone c⟩ = 1 :=
  StarStrong.starStrongLimit_eq ι hnorm hone _ (cutProj_isStarStrongLimit ι hone c)

/-- Truncation stays inside `𝒟`: it is multiplication by an element of `𝒟`. -/
theorem truncSeq_mem (c : ℕ) {x : StarStrong.BoundedStarSequence A}
    (hx : x ∈ StarStrong.starStrongSubalgebra ι hnorm hone) :
    truncSeq (A := A) c x ∈ StarStrong.starStrongSubalgebra ι hnorm hone :=
  (StarStrong.starStrongSubalgebra ι hnorm hone).mul_mem
    (cutProj_mem ι hnorm hone c) hx

/-- **Truncation is invisible to the `*`-strong limit.**  `q` is multiplicative
and kills nothing: it sends the cut projection to `1`. -/
theorem starStrongLimit_truncSeq (c : ℕ) {x : StarStrong.BoundedStarSequence A}
    (hx : x ∈ StarStrong.starStrongSubalgebra ι hnorm hone) :
    StarStrong.starStrongLimit ι hnorm hone
        ⟨truncSeq (A := A) c x, truncSeq_mem ι hnorm hone c hx⟩
      = StarStrong.starStrongLimit ι hnorm hone ⟨x, hx⟩ := by
  have hprod : (⟨truncSeq (A := A) c x, truncSeq_mem ι hnorm hone c hx⟩ :
        StarStrong.starStrongSubalgebra ι hnorm hone)
      = ⟨cutProj (A := A) c, cutProj_mem ι hnorm hone c⟩ * ⟨x, hx⟩ :=
    Subtype.ext rfl
  have hhom := StarStrong.starStrongLimitHom_apply ι hnorm hone
  calc StarStrong.starStrongLimit ι hnorm hone
        ⟨truncSeq (A := A) c x, truncSeq_mem ι hnorm hone c hx⟩
      = StarStrong.starStrongLimitHom ι hnorm hone
          (⟨cutProj (A := A) c, cutProj_mem ι hnorm hone c⟩ * ⟨x, hx⟩) := by
        rw [hhom, ← hprod]
    _ = StarStrong.starStrongLimitHom ι hnorm hone
          ⟨cutProj (A := A) c, cutProj_mem ι hnorm hone c⟩
        * StarStrong.starStrongLimitHom ι hnorm hone ⟨x, hx⟩ := map_mul _ _ _
    _ = StarStrong.starStrongLimit ι hnorm hone ⟨x, hx⟩ := by
        rw [hhom, hhom, starStrongLimit_cutProj, one_mul]

end Corner

end

end ShulmanFill
end GroupApproximation
