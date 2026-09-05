import GroupApproximation.CharClass.BundleBasic

/-!
# Complex vector bundles in the projection model, II: the rank-one calculus

Every construction with the projective bundle in this lane is an instance of one
operation: a vector `u ≠ 0` spans a line, the line is the rank-one orthogonal
projection `lineOf u`, and a matrix `a` moves the line to `lineOf (a *ᵥ u)`.
The point of writing it this way is that `a` may be **any** matrix that does not
kill `u`; it need not be unitary, and no square root, no continuous functional
calculus and no norm on `Matrix` is used anywhere.  In particular the local
trivializations of `BundleLocal.lean` are built from the invertible (but not
unitary) intertwiner `p x₀ · p x + (1 - p x₀)(1 - p x)`.

The projectivized action of `a` on a rank-one projection `r`, written without
choosing a spanning vector, is

    conjNormalize a r = (trace (a r aᴴ))⁻¹ • (a r aᴴ),

and `conjNormalize a (rankOneProj u) = lineOf (a *ᵥ u)`
(`conjNormalize_rankOneProj`) is the bridge between the two descriptions.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

section RankOne

variable {ι κ ρ : Type} [Fintype ι] [Fintype κ] [Fintype ρ]

/-! ### The squared Euclidean length -/

/-- The squared Euclidean length of a vector of `ι → ℂ`.  Vectors are plain
functions, never `EuclideanSpace`, exactly as in
`Analysis/LIXProjectiveSpaceModel.lean`; `STW59.unitVectors ι` is the level set
`eucNormSq = 1` (`mem_unitVectors_iff_eucNormSq`). -/
noncomputable def eucNormSq (u : ι → ℂ) : ℝ := ∑ i, ‖u i‖ ^ 2

theorem eucNormSq_def (u : ι → ℂ) : eucNormSq u = ∑ i, ‖u i‖ ^ 2 := rfl

theorem eucNormSq_nonneg (u : ι → ℂ) : 0 ≤ eucNormSq u :=
  Finset.sum_nonneg fun i _ => by positivity

theorem mem_unitVectors_iff_eucNormSq {u : ι → ℂ} : u ∈ unitVectors ι ↔ eucNormSq u = 1 :=
  Iff.rfl

theorem eucNormSq_eq_zero_iff {u : ι → ℂ} : eucNormSq u = 0 ↔ u = 0 := by
  constructor
  · intro h
    ext i
    have hnn : ∀ l ∈ (Finset.univ : Finset ι), (0 : ℝ) ≤ ‖u l‖ ^ 2 := fun l _ => by positivity
    have hi : ‖u i‖ ^ 2 = 0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
    have hn : ‖u i‖ = 0 := by nlinarith [norm_nonneg (u i)]
    simpa using hn
  · rintro rfl
    simp [eucNormSq_def]

theorem eucNormSq_pos {u : ι → ℂ} (hu : u ≠ 0) : 0 < eucNormSq u :=
  lt_of_le_of_ne (eucNormSq_nonneg u) fun h => hu (eucNormSq_eq_zero_iff.mp h.symm)

theorem eucNormSq_ne_zero {u : ι → ℂ} (hu : u ≠ 0) : eucNormSq u ≠ 0 :=
  ne_of_gt (eucNormSq_pos hu)

theorem continuous_eucNormSq : Continuous (eucNormSq : (ι → ℂ) → ℝ) :=
  continuous_finsetSum _ fun i _ => ((continuous_apply i).norm).pow 2

theorem eucNormSq_smul (c : ℂ) (u : ι → ℂ) : eucNormSq (c • u) = ‖c‖ ^ 2 * eucNormSq u := by
  rw [eucNormSq_def, eucNormSq_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

theorem smul_ne_zero_of_ne_zero {c : ℂ} {u : ι → ℂ} (hc : c ≠ 0) (hu : u ≠ 0) : c • u ≠ 0 := by
  intro h
  refine hu ?_
  have hn : eucNormSq (c • u) = 0 := eucNormSq_eq_zero_iff.mpr h
  rw [eucNormSq_smul] at hn
  have hc2 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  exact eucNormSq_eq_zero_iff.mp (by
    rcases mul_eq_zero.mp hn with h' | h'
    · exact absurd h' hc2
    · exact h')

/-! ### Rank-one matrices -/

theorem trace_rankOneProj_eq (u : ι → ℂ) :
    (rankOneProj u).trace = ((eucNormSq u : ℝ) : ℂ) := by
  have h : (rankOneProj u).trace = ∑ i, u i * star (u i) := rfl
  rw [h, eucNormSq_def, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => mul_star_self_eq_normSq (u i)

omit [Fintype κ] [Fintype ρ] in
theorem mul_vecMulVec (a : Matrix κ ι ℂ) (w : ι → ℂ) (y : ρ → ℂ) :
    a * Matrix.vecMulVec w y = Matrix.vecMulVec (a *ᵥ w) y := by
  ext i j
  rw [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec_apply_eq_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by rw [Matrix.vecMulVec_apply, mul_assoc]

omit [Fintype κ] [Fintype ρ] in
theorem vecMulVec_mul_conjTranspose (a : Matrix κ ι ℂ) (w : ρ → ℂ) (u : ι → ℂ) :
    Matrix.vecMulVec w (star u) * aᴴ = Matrix.vecMulVec w (star (a *ᵥ u)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply,
    Pi.star_apply, Matrix.mulVec_apply_eq_sum, star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [star_mul']
  ring

theorem mul_rankOneProj (a : Matrix κ ι ℂ) (u : ι → ℂ) :
    a * rankOneProj u = Matrix.vecMulVec (a *ᵥ u) (star u) :=
  mul_vecMulVec a u (star u)

/-- **Conjugation moves the line.**  This one identity is the reason the whole
lane needs no unitaries. -/
theorem conj_rankOneProj (a : Matrix κ ι ℂ) (u : ι → ℂ) :
    a * rankOneProj u * aᴴ = rankOneProj (a *ᵥ u) := by
  show a * Matrix.vecMulVec u (star u) * aᴴ = Matrix.vecMulVec (a *ᵥ u) (star (a *ᵥ u))
  rw [mul_vecMulVec, vecMulVec_mul_conjTranspose]

/-- A projection fixing `u` absorbs the line spanned by `u`. -/
theorem mul_rankOneProj_self {p : Matrix ι ι ℂ} {u : ι → ℂ} (h : p *ᵥ u = u) :
    p * rankOneProj u = rankOneProj u := by
  rw [mul_rankOneProj, h]
  rfl

omit [Fintype ι] in
theorem rankOneProj_smul (c : ℂ) (u : ι → ℂ) :
    rankOneProj (c • u) = ((‖c‖ ^ 2 : ℝ) : ℂ) • rankOneProj u := by
  have hc : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * star c := (mul_star_self_eq_normSq c).symm
  ext i j
  simp only [rankOneProj_apply, hc, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem continuous_rankOneProj' : Continuous (rankOneProj : (ι → ℂ) → Matrix ι ι ℂ) :=
  continuous_rankOneProj ι

/-! ### The line spanned by a nonzero vector -/

/-- **The line spanned by `u`**: the orthogonal projection onto `ℂ u`, for
`u ≠ 0`.  (For `u = 0` the formula returns `0`, which is harmless: every
statement below carries `u ≠ 0`.) -/
noncomputable def lineOf (u : ι → ℂ) : Matrix ι ι ℂ :=
  ((eucNormSq u : ℝ) : ℂ)⁻¹ • rankOneProj u

theorem lineOf_def (u : ι → ℂ) : lineOf u = ((eucNormSq u : ℝ) : ℂ)⁻¹ • rankOneProj u := rfl

theorem lineOf_apply (u : ι → ℂ) (i j : ι) :
    lineOf u i j = ((eucNormSq u : ℝ) : ℂ)⁻¹ * (u i * star (u j)) := rfl

/-- The normalization of a nonzero vector. -/
noncomputable def normalizeVec (u : ι → ℂ) : ι → ℂ :=
  (((Real.sqrt (eucNormSq u))⁻¹ : ℝ) : ℂ) • u

theorem normalizeVec_eq_smul (u : ι → ℂ) :
    normalizeVec u = (((Real.sqrt (eucNormSq u))⁻¹ : ℝ) : ℂ) • u := rfl

theorem normalizeVec_mem_unitVectors {u : ι → ℂ} (hu : u ≠ 0) :
    normalizeVec u ∈ unitVectors ι := by
  have hpos : 0 < eucNormSq u := eucNormSq_pos hu
  have hs : 0 < Real.sqrt (eucNormSq u) := Real.sqrt_pos.mpr hpos
  rw [mem_unitVectors_iff_eucNormSq, normalizeVec_eq_smul, eucNormSq_smul]
  have hnorm : ‖(((Real.sqrt (eucNormSq u))⁻¹ : ℝ) : ℂ)‖ = (Real.sqrt (eucNormSq u))⁻¹ :=
    Complex.norm_of_nonneg (le_of_lt (inv_pos.mpr hs))
  rw [hnorm, inv_pow, Real.sq_sqrt (le_of_lt hpos)]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

theorem lineOf_eq_rankOneProj_normalizeVec {u : ι → ℂ} (hu : u ≠ 0) :
    lineOf u = rankOneProj (normalizeVec u) := by
  have hpos : 0 < eucNormSq u := eucNormSq_pos hu
  have hs : 0 < Real.sqrt (eucNormSq u) := Real.sqrt_pos.mpr hpos
  have hnorm : ‖(((Real.sqrt (eucNormSq u))⁻¹ : ℝ) : ℂ)‖ = (Real.sqrt (eucNormSq u))⁻¹ :=
    Complex.norm_of_nonneg (le_of_lt (inv_pos.mpr hs))
  rw [normalizeVec_eq_smul, rankOneProj_smul, hnorm, inv_pow, Real.sq_sqrt (le_of_lt hpos),
    lineOf_def, Complex.ofReal_inv]

theorem isStarProjection_lineOf {u : ι → ℂ} (hu : u ≠ 0) : IsStarProjection (lineOf u) := by
  rw [lineOf_eq_rankOneProj_normalizeVec hu]
  exact isStarProjection_rankOneProj (normalizeVec_mem_unitVectors hu)

theorem trace_lineOf {u : ι → ℂ} (hu : u ≠ 0) : (lineOf u).trace = 1 := by
  rw [lineOf_eq_rankOneProj_normalizeVec hu]
  exact trace_rankOneProj (normalizeVec_mem_unitVectors hu)

theorem lineOf_of_mem_unitVectors {u : ι → ℂ} (hu : u ∈ unitVectors ι) :
    lineOf u = rankOneProj u := by
  rw [lineOf_def, mem_unitVectors_iff_eucNormSq.mp hu]
  simp

/-- **The line depends only on the ray**: rescaling by a nonzero scalar does not
move it.  This is what makes `lineOf` a map out of the punctured total space. -/
theorem lineOf_smul {c : ℂ} (hc : c ≠ 0) (u : ι → ℂ) : lineOf (c • u) = lineOf u := by
  have hc2 : ((‖c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  rw [lineOf_def, lineOf_def, eucNormSq_smul, rankOneProj_smul, smul_smul,
    Complex.ofReal_mul, mul_inv]
  congr 1
  rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hc2, one_mul]

/-- A projection fixing `u` absorbs the line spanned by `u`. -/
theorem mul_lineOf {p : Matrix ι ι ℂ} {u : ι → ℂ} (h : p *ᵥ u = u) : p * lineOf u = lineOf u := by
  rw [lineOf_def, Matrix.mul_smul, mul_rankOneProj_self h]

/-- The line spanned by `u` fixes `u`. -/
theorem lineOf_mulVec_self {u : ι → ℂ} (hu : u ≠ 0) : lineOf u *ᵥ u = u := by
  have hne : ((eucNormSq u : ℝ) : ℂ) ≠ 0 := by
    simpa using eucNormSq_ne_zero hu
  ext i
  rw [lineOf_def]
  have h1 : (((eucNormSq u : ℝ) : ℂ)⁻¹ • rankOneProj u) *ᵥ u
      = ((eucNormSq u : ℝ) : ℂ)⁻¹ • (rankOneProj u *ᵥ u) := Matrix.smul_mulVec _ _ _
  rw [h1, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply_eq_sum]
  have h3 : (∑ j, star (u j) * u j) = ((eucNormSq u : ℝ) : ℂ) := by
    rw [eucNormSq_def, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => star_mul_self_eq_normSq (u j)
  have hterm : ∀ j : ι, rankOneProj u i j * u j = u i * (star (u j) * u j) := by
    intro j
    rw [rankOneProj_apply]
    ring
  have h2 : (∑ j, rankOneProj u i j * u j) = ((eucNormSq u : ℝ) : ℂ) * u i := by
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm j, ← Finset.mul_sum, h3]
    ring
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem continuous_normalizeVec {Z : Type} [TopologicalSpace Z] {u : Z → ι → ℂ}
    (hu : Continuous u) (h : ∀ z, u z ≠ 0) : Continuous fun z => normalizeVec (u z) := by
  have h1 : Continuous fun z => Real.sqrt (eucNormSq (u z)) :=
    Real.continuous_sqrt.comp (continuous_eucNormSq.comp hu)
  have h2 : ∀ z, Real.sqrt (eucNormSq (u z)) ≠ 0 :=
    fun z => ne_of_gt (Real.sqrt_pos.mpr (eucNormSq_pos (h z)))
  exact (Complex.continuous_ofReal.comp (h1.inv₀ h2)).smul hu

theorem continuous_lineOf {Z : Type} [TopologicalSpace Z] {u : Z → ι → ℂ}
    (hu : Continuous u) (h : ∀ z, u z ≠ 0) : Continuous fun z => lineOf (u z) := by
  have h1 : Continuous fun z => ((eucNormSq (u z) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_eucNormSq.comp hu)
  have h2 : ∀ z, ((eucNormSq (u z) : ℝ) : ℂ) ≠ 0 := by
    intro z
    simpa using eucNormSq_ne_zero (h z)
  exact (h1.inv₀ h2).smul (continuous_rankOneProj'.comp hu)

/-! ### The projectivized action of a matrix -/

/-- The projectivized action of a matrix on a rank-one projection, written
without choosing a spanning vector. -/
noncomputable def conjNormalize (a : Matrix κ ι ℂ) (r : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  ((a * r * aᴴ).trace)⁻¹ • (a * r * aᴴ)

theorem conjNormalize_def (a : Matrix κ ι ℂ) (r : Matrix ι ι ℂ) :
    conjNormalize a r = ((a * r * aᴴ).trace)⁻¹ • (a * r * aᴴ) := rfl

theorem conjNormalize_rankOneProj (a : Matrix κ ι ℂ) (u : ι → ℂ) :
    conjNormalize a (rankOneProj u) = lineOf (a *ᵥ u) := by
  rw [conjNormalize_def, conj_rankOneProj, trace_rankOneProj_eq, lineOf_def]

theorem trace_conj_ne_zero_iff (a : Matrix κ ι ℂ) (u : ι → ℂ) :
    (a * rankOneProj u * aᴴ).trace ≠ 0 ↔ a *ᵥ u ≠ 0 := by
  rw [conj_rankOneProj, trace_rankOneProj_eq]
  constructor
  · intro h hz
    exact h (by rw [hz]; simp [eucNormSq_def])
  · intro h hz
    exact h (eucNormSq_eq_zero_iff.mp (by exact_mod_cast hz))

theorem continuous_conjNormalize {Z : Type} [TopologicalSpace Z] {a : Z → Matrix κ ι ℂ}
    {r : Z → Matrix ι ι ℂ} (ha : Continuous a) (hr : Continuous r)
    (h : ∀ z, (a z * r z * (a z)ᴴ).trace ≠ 0) :
    Continuous fun z => conjNormalize (a z) (r z) := by
  have hc : Continuous fun z => a z * r z * (a z)ᴴ :=
    (ha.matrix_mul hr).matrix_mul ha.matrix_conjTranspose
  exact (hc.matrix_trace.inv₀ h).smul hc

end RankOne

end CharClass
end GroupApproximation
