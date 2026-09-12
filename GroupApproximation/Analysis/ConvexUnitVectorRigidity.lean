import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Basic

/-!
# Convex combinations of unit vectors that stay on the sphere

Two elementary facts about a complex inner product space, isolated here
because two independent routes of the research graph need exactly them and
nothing else.  Neither uses completeness, and neither is specific to the
application.

## The statements

`eq_of_re_inner_eq_one` is the equality case of Cauchy--Schwarz for unit
vectors: if `‖x‖ = ‖y‖ = 1` and `Re ⟪x, y⟫ = 1` then `x = y`.  The proof is
the expansion `‖x - y‖² = ‖x‖² - 2 Re ⟪x, y⟫ + ‖y‖² = 1 - 2 + 1 = 0`.

`eq_sum_of_norm_sum_eq_one` is strict convexity of the unit ball, for a
finite convex combination: if `a` is a system of nonnegative weights on a
`Finset` `s` summing to `1`, every `v j` with `j ∈ s` is a unit vector, and
the combination `c = ∑ j ∈ s, a j • v j` again has norm `1`, then `v i = c`
for every `i ∈ s` of nonzero weight.  `eq_of_norm_sum_eq_one` is the pairwise
form: any two vectors carrying positive weight coincide.

## The argument

The second statement is the first applied to `c`.  Expanding the second slot
of `⟪c, c⟫` against the combination and taking real parts gives

`1 = ‖c‖² = Re ⟪c, c⟫ = ∑ j ∈ s, a j · Re ⟪c, v j⟫`,

while Cauchy--Schwarz caps each factor by `Re ⟪c, v j⟫ ≤ ‖c‖ ‖v j‖ = 1`.  So
`1` is exhibited as a convex mean of numbers at most `1`, and a mean of such
numbers equals `1` only when every term of nonzero weight does; the equality
case then identifies `v i` with `c`.

The expansion is taken in the second argument throughout, where `inner` is
linear rather than conjugate-linear, so no conjugation ever appears.  Real
weights act through their complex coercion (`Complex.coe_smul`), which is the
only place the real module structure of the ambient complex space is used.

## Consumers

* `sl3-collapse-from-single-hecke-average-isometry` reads the Hecke average
  `S(k)` as a convex combination of `L + 1` unit vectors of `L²(M)` and turns
  the isometry `‖S(k)‖₂ = 1` into `π(wᵢ) k π(wᵢ)* = k` for every `i`, which is
  what promotes the single norm equality to the relative commutant collapse.
* `rcc-carrier-character-face-compression-proof` uses the equality case of
  Cauchy--Schwarz on the carrier-character face.
-/

namespace GroupApproximation
namespace ConvexUnitVectorRigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Equality in Cauchy--Schwarz for unit vectors.**  Two unit vectors whose
inner product has real part `1` are equal, because
`‖x - y‖² = ‖x‖² - 2 Re ⟪x, y⟫ + ‖y‖²` then vanishes. -/
theorem eq_of_re_inner_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : RCLike.re (inner ℂ x y) = 1) : x = y := by
  have hsq : ‖x - y‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ) x y, hx, hy, hxy]
    norm_num
  have hzero : ‖x - y‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- **Strict convexity of the unit sphere, for a finite convex combination.**
If nonnegative weights summing to `1` combine unit vectors into a vector that
is again a unit vector, then every vector carrying nonzero weight *is* the
combination. -/
theorem eq_sum_of_norm_sum_eq_one {ι : Type*} {s : Finset ι} {a : ι → ℝ}
    {v : ι → E} (ha : ∀ j ∈ s, 0 ≤ a j) (hone : ∑ j ∈ s, a j = 1)
    (hv : ∀ j ∈ s, ‖v j‖ = 1) (hnorm : ‖∑ j ∈ s, a j • v j‖ = 1)
    {i : ι} (hi : i ∈ s) (hai : a i ≠ 0) :
    v i = ∑ j ∈ s, a j • v j := by
  -- A real scalar acts as its complex coercion, so the sum is a `ℂ`-combination.
  have hcoe : ∀ (r : ℝ) (z : E), r • z = ((r : ℂ)) • z :=
    fun r z ↦ (Complex.coe_smul r z).symm
  -- Pairing anything against the combination pairs it against the pieces.  The
  -- combination sits in the second slot, where `inner` is `ℂ`-linear.
  have hexp : ∀ w : E, RCLike.re (inner ℂ w (∑ j ∈ s, a j • v j))
      = ∑ j ∈ s, a j * RCLike.re (inner ℂ w (v j)) := by
    intro w
    have hrw : (∑ j ∈ s, a j • v j) = ∑ j ∈ s, ((a j : ℂ)) • v j :=
      Finset.sum_congr rfl fun j _ ↦ hcoe (a j) (v j)
    rw [hrw, inner_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [inner_smul_right]
    exact Complex.re_ofReal_mul (a j) (inner ℂ w (v j))
  set c : E := ∑ j ∈ s, a j • v j
  -- The combination is a unit vector, so it pairs with itself to `1`.
  have hself : RCLike.re (inner ℂ c c) = 1 := by
    rw [inner_self_eq_norm_sq (𝕜 := ℂ) c, hnorm, one_pow]
  -- Cauchy--Schwarz caps every pairing against a piece by `1`.
  have hle : ∀ j ∈ s, RCLike.re (inner ℂ c (v j)) ≤ 1 := by
    intro j hj
    have h := re_inner_le_norm (𝕜 := ℂ) c (v j)
    rw [hnorm, hv j hj, one_mul] at h
    exact h
  -- So `1` is a convex mean of numbers at most `1`.
  have htotal : ∑ j ∈ s, a j * RCLike.re (inner ℂ c (v j)) = 1 :=
    (hexp c).symm.trans hself
  -- A term of nonzero weight falling short would make the mean fall short.
  have hterm : RCLike.re (inner ℂ c (v i)) = 1 := by
    by_contra hne
    have hlt : RCLike.re (inner ℂ c (v i)) < 1 := lt_of_le_of_ne (hle i hi) hne
    have hpos : 0 < a i := lt_of_le_of_ne (ha i hi) (Ne.symm hai)
    have hstrict : ∑ j ∈ s, a j * RCLike.re (inner ℂ c (v j)) < ∑ j ∈ s, a j * 1 :=
      Finset.sum_lt_sum (fun j hj ↦ mul_le_mul_of_nonneg_left (hle j hj) (ha j hj))
        ⟨i, hi, mul_lt_mul_of_pos_left hlt hpos⟩
    rw [htotal] at hstrict
    simp only [mul_one] at hstrict
    linarith
  exact (eq_of_re_inner_eq_one hnorm (hv i hi) hterm).symm

/-- **The pairwise form.**  Under the hypotheses of
`eq_sum_of_norm_sum_eq_one`, all the unit vectors carrying nonzero weight
coincide. -/
theorem eq_of_norm_sum_eq_one {ι : Type*} {s : Finset ι} {a : ι → ℝ}
    {v : ι → E} (ha : ∀ k ∈ s, 0 ≤ a k) (hone : ∑ k ∈ s, a k = 1)
    (hv : ∀ k ∈ s, ‖v k‖ = 1) (hnorm : ‖∑ k ∈ s, a k • v k‖ = 1)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hai : a i ≠ 0) (haj : a j ≠ 0) :
    v i = v j :=
  (eq_sum_of_norm_sum_eq_one ha hone hv hnorm hi hai).trans
    (eq_sum_of_norm_sum_eq_one ha hone hv hnorm hj haj).symm

end ConvexUnitVectorRigidity
end GroupApproximation
