import GroupApproximation.Analysis.LIXClutching
import GroupApproximation.Analysis.LIXProjectiveSpaceModel

/-!
# The explicit generator for STW Problem LIX

`§3` of `research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`
fixes a based map `u : S⁴ → U(2)` representing the nonzero element of
`π₄(U(2)) ≅ ℤ/2`.  This file pins that map down by a closed formula, so that
nothing in the development depends on an unnamed representative.

## The formula

Write `S⁴ ⊆ ℂ² × ℝ`, a point being `((z,w), s)` with
`|z|² + |w|² + s² = 1`, and put `r = (|z|²+|w|²)^{1/2}`.  Then

```text
u(z,w,s) = ⎡ s + i(|z|²-|w|²)/r        2 z w̄ / r      ⎤
           ⎣    -2 z̄ w / r        s - i(|z|²-|w|²)/r  ⎦
```

In quaternion form this is `u(v,s) = s + v i v̄ / |v|` for `v ∈ ℍ = ℝ⁴`: the
suspension parameter is `s`, and at each latitude the equatorial `S³` is sent
to `S² ⊆ Im ℍ` by the Hopf map `v ↦ v i v̄`, rescaled by `|v|`.  So `u = Ση`,
the suspension of the Hopf map, which is the standard generator.

Two features of the formula are deliberate.  The scaling by `1/r` rather than
`1/r²` is what makes the entries `O(r)` and hence the map continuous at the two
poles, where the Hopf direction has no limit at all -- the same damping trick as
in `LIXClutching.continuous_damped`.  And Lean's `x / 0 = 0` makes the formula
*total*: at the poles it evaluates to `± 1` with no case split in the
definition.

## Main results

* `hopfSuspension_normSq` -- `|α|² + |β|² = 1` on `S⁴`, so the matrix is in
  `SU(2)`.
* `su2_conjTranspose_mul_self`, `su2_mul_conjTranspose` -- the `SU(2)` shape is
  unitary; hence so is `hopfSuspension` (`hopfSuspension_unitary`).
* `continuous_hopfSuspension` -- continuity, poles included.

## What is *not* proved here, and why

The manuscript's §3 also asserts two facts about `u`:

* (i) `u²` is null-homotopic in `U(2)`-valued maps on `S⁴`;
* (ii) `u ⊕ 1 : S⁴ → U(3)` is null-homotopic.

Neither is elementary.  The manuscript takes both from Bott's unstable
computation `π₄(U(2)) ≅ ℤ/2`, `π₄(U(3)) = 0` [Bott, p. 315], and there is no
explicit contraction to be had:

* (i) is exactly `2·Ση = 0` in `π₄(S³) = ℤ/2`.  Every homotopy of the shape
  `cos g_τ(θ) + sin g_τ(θ)·η̂` (with `s = cos θ`) is obstructed: continuity at
  the poles forces `g_τ(0), g_τ(π) ∈ πℤ`, these are locally constant in `τ`,
  so `g_τ(0) = 0` and `g_τ(π) = 2π` throughout, and a constant end map would
  need `g_1` to be `πℤ`-valued, continuous and non-constant.  So a
  null-homotopy has to leave the family entirely, which is the content of the
  Freudenthal/EHP computation.
* (ii) follows from an explicit pair of local sections `σ_± : D_± → U(3)` of
  the frame fibration `a ↦ a e₃` over the two closed hemispheres of `S⁵`,
  whose seam discrepancy is `u`; the same pair also gives `clutch u ≅ F`.  But
  the planar-rotation ansatz for such a section is singular on the great
  `S³ = {x₃ = 0}`, which meets both hemispheres whatever equator is chosen, and
  the phase cannot be repaired: on each level set `{|x₃| = 1-ε} ≅ S¹ × S³` the
  required phase is homotopic to the `S¹`-projection, which does not extend
  inwards.  That obstruction *is* the nontriviality of `F`.

They are therefore recorded as named propositions, `SquareNullHomotopy` and
`StableNullHomotopy`, with no instance and no use inside any endpoint.

Neither is needed for the negative answer to Problem LIX.  Failure of
`K₁`-injectivity needs `v ∉ U₀(A)` together with `[v] = 0` in `K₁(A)`, and
`K₁(A) = 0` (manuscript Lemma 5) supplies the latter outright; (i) upgrades
"nonzero" to "of order exactly two", and (ii) is an alternative route to
stable triviality.  Details in
`research/artifacts/stw59-clutching-layer-and-generator-cost-2026-09-05.md`.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

/-! ## The `SU(2)` shape -/

/-- The generic element of `SU(2)`, as a `2 × 2` complex matrix. -/
def su2 (α β : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α]

theorem su2_conjTranspose (α β : ℂ) :
    (su2 α β)ᴴ = !![(starRingEnd ℂ) α, -β; (starRingEnd ℂ) β, α] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2, Matrix.conjTranspose_apply]

/-- The defining relation in complex-multiplicative form. -/
theorem su2_norm_relation {α β : ℂ} (h : Complex.normSq α + Complex.normSq β = 1) :
    (starRingEnd ℂ) α * α + (starRingEnd ℂ) β * β = 1 := by
  rw [mul_comm ((starRingEnd ℂ) α) α, mul_comm ((starRingEnd ℂ) β) β,
    Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, h, Complex.ofReal_one]

theorem su2_conjTranspose_mul_self {α β : ℂ} (h : Complex.normSq α + Complex.normSq β = 1) :
    (su2 α β)ᴴ * su2 α β = 1 := by
  have hn := su2_norm_relation h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2, su2_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    first
      | ring1
      | linear_combination hn

theorem su2_mul_conjTranspose {α β : ℂ} (h : Complex.normSq α + Complex.normSq β = 1) :
    su2 α β * (su2 α β)ᴴ = 1 := by
  have hn := su2_norm_relation h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2, su2_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    first
      | ring1
      | linear_combination hn

/-! ## The generator -/

/-- The radius of the equatorial part of a point of `S⁴ ⊆ ℂ² × ℝ`. -/
def eqRadius (z w : ℂ) : ℝ := Real.sqrt (Complex.normSq z + Complex.normSq w)

theorem eqRadius_nonneg (z w : ℂ) : 0 ≤ eqRadius z w := Real.sqrt_nonneg _

theorem eqRadius_sq (z w : ℂ) : eqRadius z w ^ 2 = Complex.normSq z + Complex.normSq w :=
  Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg z) (Complex.normSq_nonneg w))

/-- The diagonal coefficient of the generator: the height component of the
rescaled Hopf map. -/
def hopfDiag (z w : ℂ) : ℝ := (Complex.normSq z - Complex.normSq w) / eqRadius z w

/-- The off-diagonal coefficient of the generator: the complex component of the
rescaled Hopf map. -/
def hopfOff (z w : ℂ) : ℂ := ((2 / eqRadius z w : ℝ) : ℂ) * (z * (starRingEnd ℂ) w)

/-- **The explicit generator** `u = Ση : S⁴ → SU(2)`, as a total formula on
`ℂ × ℂ × ℝ`. -/
def hopfSuspension (z w : ℂ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  su2 ((s : ℂ) + ((hopfDiag z w : ℝ) : ℂ) * Complex.I) (hopfOff z w)

/-- **The generator lands in `SU(2)`.**  This is the identity
`(|z|²-|w|²)² + 4|z|²|w|² = (|z|²+|w|²)²` together with `|z|²+|w|²+s² = 1`. -/
theorem hopfSuspension_normSq {z w : ℂ} {s : ℝ}
    (h : Complex.normSq z + Complex.normSq w + s ^ 2 = 1) :
    Complex.normSq ((s : ℂ) + ((hopfDiag z w : ℝ) : ℂ) * Complex.I)
      + Complex.normSq (hopfOff z w) = 1 := by
  have hA : Complex.normSq ((s : ℂ) + ((hopfDiag z w : ℝ) : ℂ) * Complex.I)
      = s ^ 2 + hopfDiag z w ^ 2 := Complex.normSq_add_mul_I s (hopfDiag z w)
  have hB : Complex.normSq (hopfOff z w)
      = (2 / eqRadius z w) ^ 2 * (Complex.normSq z * Complex.normSq w) := by
    rw [hopfOff, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_conj]
    ring
  rw [hA, hB]
  rcases eq_or_ne (eqRadius z w) 0 with hr | hr
  · have hr2 : Complex.normSq z + Complex.normSq w = 0 := by
      rw [← eqRadius_sq, hr]; ring
    have hd : hopfDiag z w = 0 := by rw [hopfDiag, hr, div_zero]
    have hz : (2 / (0 : ℝ)) ^ 2 * (Complex.normSq z * Complex.normSq w) = 0 := by norm_num
    rw [hd, hr, hz]
    linarith [h, hr2]
  · have hr2 : eqRadius z w ^ 2 = Complex.normSq z + Complex.normSq w := eqRadius_sq z w
    have hAB : Complex.normSq z + Complex.normSq w ≠ 0 := by
      rw [← hr2]
      exact pow_ne_zero 2 hr
    have key : hopfDiag z w ^ 2
        + (2 / eqRadius z w) ^ 2 * (Complex.normSq z * Complex.normSq w)
        = Complex.normSq z + Complex.normSq w := by
      rw [hopfDiag, div_pow, div_pow, hr2]
      field_simp
      ring
    linarith [key, h]

/-- The generator is unitary at every point of `S⁴`. -/
theorem hopfSuspension_unitary {z w : ℂ} {s : ℝ}
    (h : Complex.normSq z + Complex.normSq w + s ^ 2 = 1) :
    (hopfSuspension z w s)ᴴ * hopfSuspension z w s = 1 ∧
      hopfSuspension z w s * (hopfSuspension z w s)ᴴ = 1 :=
  ⟨su2_conjTranspose_mul_self (hopfSuspension_normSq h),
    su2_mul_conjTranspose (hopfSuspension_normSq h)⟩

/-! ## Continuity, poles included -/

theorem abs_hopfDiag_le (z w : ℂ) : |hopfDiag z w| ≤ eqRadius z w := by
  rcases eq_or_ne (eqRadius z w) 0 with hr | hr
  · rw [hopfDiag, hr, div_zero, abs_zero]
  · have hpos : 0 < eqRadius z w := lt_of_le_of_ne (eqRadius_nonneg z w) (Ne.symm hr)
    rw [hopfDiag, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have hsq : eqRadius z w * eqRadius z w = Complex.normSq z + Complex.normSq w := by
      rw [← sq]; exact eqRadius_sq z w
    rw [hsq, abs_le]
    constructor <;>
      nlinarith [Complex.normSq_nonneg z, Complex.normSq_nonneg w]

theorem norm_hopfOff_le (z w : ℂ) : ‖hopfOff z w‖ ≤ eqRadius z w := by
  rcases eq_or_ne (eqRadius z w) 0 with hr | hr
  · rw [hopfOff, hr]
    norm_num
  · have hpos : 0 < eqRadius z w := lt_of_le_of_ne (eqRadius_nonneg z w) (Ne.symm hr)
    have hsq : eqRadius z w * eqRadius z w = Complex.normSq z + Complex.normSq w := by
      rw [← sq]; exact eqRadius_sq z w
    have hnz : ‖z‖ ^ 2 = Complex.normSq z := (Complex.normSq_eq_norm_sq z).symm
    have hnw : ‖w‖ ^ 2 = Complex.normSq w := (Complex.normSq_eq_norm_sq w).symm
    rw [hopfOff, norm_mul, norm_mul, Complex.norm_real, RCLike.norm_conj,
      Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos, hsq]
    have h2 : 2 * ‖z‖ * ‖w‖ ≤ ‖z‖ ^ 2 + ‖w‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - ‖w‖)]
    have h2abs : |(2 : ℝ)| = 2 := by norm_num
    rw [← hnz, ← hnw, h2abs]
    nlinarith [norm_nonneg z, norm_nonneg w, h2]

theorem continuous_eqRadius : Continuous fun p : ℂ × ℂ => eqRadius p.1 p.2 :=
  Real.continuous_sqrt.comp
    ((Complex.continuous_normSq.comp continuous_fst).add
      (Complex.continuous_normSq.comp continuous_snd))

theorem continuous_hopfDiag : Continuous fun p : ℂ × ℂ => hopfDiag p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  intro p
  rcases eq_or_ne (eqRadius p.1 p.2) 0 with hr | hr
  · refine continuousAt_of_norm_le (r := fun q : ℂ × ℂ => eqRadius q.1 q.2)
      (fun q => by simpa [Real.norm_eq_abs] using abs_hopfDiag_le q.1 q.2) ?_ ?_
    · have h0 : Filter.Tendsto (fun q : ℂ × ℂ => eqRadius q.1 q.2) (nhds p)
          (nhds (eqRadius p.1 p.2)) := continuous_eqRadius.continuousAt
      rwa [hr] at h0
    · rw [hopfDiag, hr, div_zero]
  · exact ContinuousAt.div
      (((Complex.continuous_normSq.comp continuous_fst).sub
        (Complex.continuous_normSq.comp continuous_snd)).continuousAt)
      continuous_eqRadius.continuousAt hr

theorem continuous_hopfOff : Continuous fun p : ℂ × ℂ => hopfOff p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  intro p
  rcases eq_or_ne (eqRadius p.1 p.2) 0 with hr | hr
  · refine continuousAt_of_norm_le (r := fun q : ℂ × ℂ => eqRadius q.1 q.2)
      (fun q => norm_hopfOff_le q.1 q.2) ?_ ?_
    · have h0 : Filter.Tendsto (fun q : ℂ × ℂ => eqRadius q.1 q.2) (nhds p)
          (nhds (eqRadius p.1 p.2)) := continuous_eqRadius.continuousAt
      rwa [hr] at h0
    · rw [hopfOff, hr]
      norm_num
  · have hden : ContinuousAt (fun q : ℂ × ℂ => ((2 / eqRadius q.1 q.2 : ℝ) : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        (ContinuousAt.div continuousAt_const continuous_eqRadius.continuousAt hr)
    exact hden.mul ((continuous_fst.mul (Complex.continuous_conj.comp
      continuous_snd)).continuousAt)

theorem continuous_hopfSuspension :
    Continuous fun p : (ℂ × ℂ) × ℝ => hopfSuspension p.1.1 p.1.2 p.2 := by
  have hd : Continuous fun p : (ℂ × ℂ) × ℝ => ((hopfDiag p.1.1 p.1.2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_hopfDiag.comp continuous_fst)
  have ho : Continuous fun p : (ℂ × ℂ) × ℝ => hopfOff p.1.1 p.1.2 :=
    continuous_hopfOff.comp continuous_fst
  have hs : Continuous fun p : (ℂ × ℂ) × ℝ => ((p.2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_snd
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [hopfSuspension, su2, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Matrix.head_fin_const]
  · exact hs.add (hd.mul continuous_const)
  · exact ho
  · exact (Complex.continuous_conj.comp ho).neg
  · exact Complex.continuous_conj.comp (hs.add (hd.mul continuous_const))

/-! ## The two propositions owed to Bott's computation -/

section Owed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Owed input (i): `u²` is null-homotopic.**

`SquareNullHomotopy w` says that the pointwise square of `w` extends to a
continuous unitary-valued map on the closed unit ball of `E` which is the
identity at the centre -- which is exactly null-homotopy of `w²`, in the disc
form used by `LIXClutching.IsDiscUnitary`.

For the generator of `π₄(U(2))` this is the statement that its class has order
dividing two, i.e. Bott's `π₄(U(2)) ≅ ℤ/2`.  It is **not** proved here, it has
no instance in this development, and no endpoint mentions it.  It is not
needed for the negative answer to Problem LIX; it upgrades the conclusion from
"the class is nonzero" to "the class has order exactly two". -/
def SquareNullHomotopy (w : E → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ Ω : E → Matrix (Fin 2) (Fin 2) ℂ, IsDiscUnitary Ω ∧ ∀ y : E, ‖y‖ = 1 → Ω y = w y * w y

/-- **Owed input (ii): `u ⊕ 1` is null-homotopic in `U(3)`.**

`StableNullHomotopy w` says that the block sum `w ⊕ 1` extends to a continuous
unitary-valued map on the closed unit ball of `E` which is the identity at the
centre.

For the generator of `π₄(U(2))` this is Bott's `π₄(U(3)) = 0`.  Equivalently
it follows from an explicit pair of local sections of the frame fibration
`U(2) → U(3) → S⁵` over the two closed hemispheres, whose seam discrepancy is
`u`; that same pair also identifies `clutch u` with the tautological complement
`F : x ↦ 1 - x xᴴ`, so the two inputs are one object.  It is **not** proved
here, it has no instance, and no endpoint mentions it. -/
def StableNullHomotopy (w : E → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ Ω : E → Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ, IsDiscUnitary Ω ∧
    ∀ y : E, ‖y‖ = 1 → Ω y = Matrix.fromBlocks (w y) 0 0 1

end Owed

/-! ## Hemisphere frames of the tautological complement over `S⁵`

`§3` of the manuscript fixes `u` as the seam discrepancy of hemisphere
trivialisations of the frame fibration `U(3) → S⁵`, `a ↦ a e₃`, and takes from
Bott that `diag(u,1)` is null-homotopic in `U(3)`.  Neither the
trivialisations nor the null-homotopy need any input from homotopy theory:
both are written down here, and the "not elementary" finding recorded in
`research/artifacts/stw59-clutching-layer-and-generator-cost-2026-09-05.md`
§3.2 is wrong -- it rules out one ansatz and over-generalises.

The one thing that has to be got right is the **domain**.  Transporting a
frame from a fixed base point `p` to `x` is possible exactly when `pᴴx ≠ 0`,
and `{x : pᴴx = 0}` is a 3-sphere which meets both closed hemispheres whatever
equator is chosen: that, and not any homotopy-theoretic obstruction, is what
defeats every one-step formula.  Two steps through the normalised midpoint
remove it.  Both inner products that then have to be nonzero are the *same*
number `(1 + pᴴx)/‖p + x‖`, and `‖p + x‖` vanishes only at `x = -p`, so the
composite is defined on the whole sphere minus one point -- far more than a
closed hemisphere needs.

The ingredients are elementary:

* `reflMat v = 1 - (2/(vᴴv))·v vᴴ`, the Householder reflection: self-adjoint
  and an involution, hence unitary, with no functional calculus and no polar
  decomposition.
* `reflMat (a + b) * reflMat a` carries the unit vector `a` to the unit vector
  `b` whenever `aᴴb` is real; `transportRot` rephases the target by
  `aᴴb/‖aᴴb‖` to remove the reality condition.
* `frameRot p x` composes two of those through the midpoint.

Everything is stated for `n → ℂ` with `dotProduct`, never with `‖·‖`: the
product type carries the sup norm, so `‖x‖ = 1` is the wrong condition, and
`STW59.sum_star_mul_self` is the bridge from `STW59.unitVectors`.
-/

section Frames

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Rank-one matrices -/

/-- `rk1 u v` is the rank-one matrix `u vᴴ`, the two-vector generalisation of
`STW59.rankOneProj`. -/
def rk1 (u v : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec u (star v)

theorem rk1_apply (u v : n → ℂ) (i j : n) : rk1 u v i j = u i * star (v j) := rfl

theorem rk1_self (x : n → ℂ) : rk1 x x = STW59.rankOneProj x := rfl

theorem rk1_conjTranspose (u v : n → ℂ) : (rk1 u v)ᴴ = rk1 v u := by
  simp only [rk1, Matrix.conjTranspose_vecMulVec, star_star]

theorem rk1_mul (u v p w : n → ℂ) :
    rk1 u v * rk1 p w = (star v ⬝ᵥ p) • rk1 u w := by
  simp only [rk1, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]

theorem rk1_smul_left (c : ℂ) (u v : n → ℂ) : rk1 (c • u) v = c • rk1 u v := by
  simp only [rk1, Matrix.smul_vecMulVec]

theorem rk1_add_left (u u' v : n → ℂ) : rk1 (u + u') v = rk1 u v + rk1 u' v :=
  Matrix.add_vecMulVec _ _ _

theorem rk1_neg_left (u v : n → ℂ) : rk1 (-u) v = -rk1 u v :=
  Matrix.neg_vecMulVec _ _

theorem continuous_rk1 {X : Type*} [TopologicalSpace X] {u v : X → n → ℂ}
    (hu : Continuous u) (hv : Continuous v) :
    Continuous fun x => rk1 (u x) (v x) :=
  Continuous.matrix_vecMulVec hu hv.star

/-! ### The inner product `star a ⬝ᵥ b` -/

theorem star_dotProduct_comm (a b : n → ℂ) :
    star b ⬝ᵥ a = star (star a ⬝ᵥ b) := by
  show (∑ i, star (b i) * a i) = star (∑ i, star (a i) * b i)
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul', star_star, mul_comm]

theorem star_dotProduct_self_star (v : n → ℂ) :
    star (star v ⬝ᵥ v) = star v ⬝ᵥ v :=
  (star_dotProduct_comm v v).symm

theorem star_dotProduct_self_ofReal (v : n → ℂ) :
    star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  show (∑ i, star (v i) * v i) = _
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => STW59.star_mul_self_eq_normSq (v i)

theorem star_dotProduct_self_re (v : n → ℂ) :
    (star v ⬝ᵥ v).re = ∑ i, ‖v i‖ ^ 2 := by
  rw [star_dotProduct_self_ofReal, Complex.ofReal_re]

theorem star_dotProduct_self_re_nonneg (v : n → ℂ) : 0 ≤ (star v ⬝ᵥ v).re := by
  rw [star_dotProduct_self_re]
  exact Finset.sum_nonneg fun i _ => by positivity

theorem eq_zero_of_star_dotProduct_self_eq_zero {v : n → ℂ}
    (h : star v ⬝ᵥ v = 0) : v = 0 := by
  have h2 : (∑ i, ‖v i‖ ^ 2 : ℝ) = 0 := by
    have hc := star_dotProduct_self_ofReal v
    rw [h] at hc
    exact_mod_cast hc.symm
  funext i
  have hle : ‖v i‖ ^ 2 ≤ ∑ k, ‖v k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun k _ => by positivity)
      (Finset.mem_univ i)
  have hi : ‖v i‖ = 0 := by nlinarith [norm_nonneg (v i)]
  simpa using hi

theorem star_add_dotProduct (a b c : n → ℂ) :
    star (a + b) ⬝ᵥ c = star a ⬝ᵥ c + star b ⬝ᵥ c := by
  rw [star_add, add_dotProduct]

theorem star_dotProduct_add (a b c : n → ℂ) :
    star a ⬝ᵥ (b + c) = star a ⬝ᵥ b + star a ⬝ᵥ c := dotProduct_add _ _ _

theorem star_smul_dotProduct (c : ℂ) (a b : n → ℂ) :
    star (c • a) ⬝ᵥ b = star c * (star a ⬝ᵥ b) := by
  rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem star_dotProduct_smul (c : ℂ) (a b : n → ℂ) :
    star a ⬝ᵥ (c • b) = c * (star a ⬝ᵥ b) := by
  rw [dotProduct_smul, smul_eq_mul]

/-! ### The Householder reflection -/

/-- The reflection in the hyperplane orthogonal to `v`. -/
def reflMat (v : n → ℂ) : Matrix n n ℂ := 1 - ((2 : ℂ) / (star v ⬝ᵥ v)) • rk1 v v

theorem reflMat_conjTranspose (v : n → ℂ) : (reflMat v)ᴴ = reflMat v := by
  have hs : star ((2 : ℂ) / (star v ⬝ᵥ v)) = (2 : ℂ) / (star v ⬝ᵥ v) := by
    rw [star_div₀, star_dotProduct_self_star]
    norm_num
  simp only [reflMat, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, rk1_conjTranspose, hs]

/-- Left multiplication by a reflection, on a rank-one matrix. -/
theorem reflMat_mul_rk1 (v u w : n → ℂ) :
    reflMat v * rk1 u w
      = rk1 u w - ((2 : ℂ) / (star v ⬝ᵥ v) * (star v ⬝ᵥ u)) • rk1 v w := by
  rw [reflMat, sub_mul, Matrix.one_mul, Matrix.smul_mul, rk1_mul, smul_smul]

theorem reflMat_mul_rk1_self {v : n → ℂ} (hv : star v ⬝ᵥ v ≠ 0) (w : n → ℂ) :
    reflMat v * rk1 v w = -rk1 v w := by
  rw [reflMat_mul_rk1, div_mul_cancel₀ _ hv, two_smul]
  abel

/-- A reflection is an involution, hence -- being self-adjoint -- unitary. -/
theorem reflMat_mul_self {v : n → ℂ} (hv : star v ⬝ᵥ v ≠ 0) :
    reflMat v * reflMat v = 1 := by
  have ht : (2 : ℂ) / (star v ⬝ᵥ v) * (star v ⬝ᵥ v) = 2 := div_mul_cancel₀ _ hv
  have hcoef : (2 : ℂ) / (star v ⬝ᵥ v) * ((2 : ℂ) / (star v ⬝ᵥ v) * (star v ⬝ᵥ v))
      = 2 * ((2 : ℂ) / (star v ⬝ᵥ v)) := by
    rw [ht, mul_comm]
  have hP : rk1 v v * rk1 v v = (star v ⬝ᵥ v) • rk1 v v := rk1_mul v v v v
  simp only [reflMat, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hP, smul_smul]
  rw [hcoef, two_mul, add_smul]
  abel

theorem reflMat_conjTranspose_mul_self {v : n → ℂ} (hv : star v ⬝ᵥ v ≠ 0) :
    (reflMat v)ᴴ * reflMat v = 1 := by
  rw [reflMat_conjTranspose, reflMat_mul_self hv]

/-! ### The unitary transport -/

/-- The phase of `aᴴ b`. -/
def transPhase (a b : n → ℂ) : ℂ := (star a ⬝ᵥ b) / ((‖star a ⬝ᵥ b‖ : ℝ) : ℂ)

/-- The target of the transport, rephased so that its inner product with `a`
is real and nonnegative.  This is the only place the complex phase enters, and
it is what makes the two-reflection formula apply. -/
def transTarget (a b : n → ℂ) : n → ℂ := star (transPhase a b) • b

/-- **The unitary transport.**  An explicit unitary carrying the unit vector
`a` to the unit vector `b`, defined whenever `aᴴ b ≠ 0`.  It acts as the
scalar `transPhase a b`, not as the identity, off `span {a, b}`; that is
harmless, and it is what keeps the formula continuous. -/
def transportRot (a b : n → ℂ) : Matrix n n ℂ :=
  transPhase a b • (reflMat (a + transTarget a b) * reflMat a)

/-- The hypotheses under which `transportRot a b` carries `a` to `b`. -/
structure IsTransportDatum (a b : n → ℂ) : Prop where
  unit_a : star a ⬝ᵥ a = 1
  unit_b : star b ⬝ᵥ b = 1
  inner_ne : star a ⬝ᵥ b ≠ 0

namespace IsTransportDatum

variable {a b : n → ℂ}

theorem ofReal_norm_ne_zero (h : IsTransportDatum a b) :
    ((‖star a ⬝ᵥ b‖ : ℝ) : ℂ) ≠ 0 := by
  simpa using h.inner_ne

theorem star_ofReal_norm (a b : n → ℂ) :
    star (((‖star a ⬝ᵥ b‖ : ℝ) : ℂ)) = ((‖star a ⬝ᵥ b‖ : ℝ) : ℂ) := by
  simp

theorem transPhase_mul_star (h : IsTransportDatum a b) :
    transPhase a b * star (transPhase a b) = 1 := by
  have hn := h.ofReal_norm_ne_zero
  have hz : (star a ⬝ᵥ b) * star (star a ⬝ᵥ b)
      = ((‖star a ⬝ᵥ b‖ : ℝ) : ℂ) * ((‖star a ⬝ᵥ b‖ : ℝ) : ℂ) := by
    rw [STW59.mul_star_self_eq_normSq]
    push_cast
    ring
  rw [transPhase, star_div₀, star_ofReal_norm, div_mul_div_comm, hz,
    div_self (mul_ne_zero hn hn)]

theorem star_transPhase_mul (h : IsTransportDatum a b) :
    star (transPhase a b) * transPhase a b = 1 := by
  rw [mul_comm]; exact h.transPhase_mul_star

theorem unit_target (h : IsTransportDatum a b) :
    star (transTarget a b) ⬝ᵥ transTarget a b = 1 := by
  rw [transTarget, star_smul_dotProduct, star_dotProduct_smul, h.unit_b, mul_one,
    star_star, h.transPhase_mul_star]

theorem inner_target (h : IsTransportDatum a b) :
    star a ⬝ᵥ transTarget a b = ((‖star a ⬝ᵥ b‖ : ℝ) : ℂ) := by
  have hn := h.ofReal_norm_ne_zero
  have hz : star (star a ⬝ᵥ b) * (star a ⬝ᵥ b)
      = ((‖star a ⬝ᵥ b‖ : ℝ) : ℂ) * ((‖star a ⬝ᵥ b‖ : ℝ) : ℂ) := by
    rw [STW59.star_mul_self_eq_normSq]
    push_cast
    ring
  rw [transTarget, star_dotProduct_smul, transPhase, star_div₀, star_ofReal_norm,
    div_mul_eq_mul_div, hz, mul_div_assoc, div_self hn, mul_one]

theorem inner_target_symm (h : IsTransportDatum a b) :
    star (transTarget a b) ⬝ᵥ a = ((‖star a ⬝ᵥ b‖ : ℝ) : ℂ) := by
  rw [star_dotProduct_comm, h.inner_target, star_ofReal_norm]

/-- The sum `a + b~` has squared length `2 + 2‖aᴴb‖`, which is at least `2`. -/
theorem inner_sum (h : IsTransportDatum a b) :
    star (a + transTarget a b) ⬝ᵥ (a + transTarget a b)
      = 2 + 2 * ((‖star a ⬝ᵥ b‖ : ℝ) : ℂ) := by
  rw [star_add_dotProduct, star_dotProduct_add, star_dotProduct_add, h.unit_a,
    h.inner_target, h.inner_target_symm, h.unit_target]
  ring

theorem inner_sum_ne (h : IsTransportDatum a b) :
    star (a + transTarget a b) ⬝ᵥ (a + transTarget a b) ≠ 0 := by
  rw [h.inner_sum]
  have hnn : (0 : ℝ) ≤ ‖star a ⬝ᵥ b‖ := norm_nonneg _
  intro hc
  have hre : (2 : ℝ) + 2 * ‖star a ⬝ᵥ b‖ = 0 := by
    have := congrArg Complex.re hc
    simpa using this
  linarith

/-- The scalar identity `2/(2 + 2k) * (1 + k) = 1` that makes the second
reflection land exactly on the target. -/
theorem sum_coeff (h : IsTransportDatum a b) :
    (2 : ℂ) / (star (a + transTarget a b) ⬝ᵥ (a + transTarget a b))
        * (star (a + transTarget a b) ⬝ᵥ a) = 1 := by
  have hk : (1 : ℂ) + ((‖star a ⬝ᵥ b‖ : ℝ) : ℂ) ≠ 0 := by
    intro hc
    have hre : (1 : ℝ) + ‖star a ⬝ᵥ b‖ = 0 := by
      have := congrArg Complex.re hc
      simpa using this
    have := norm_nonneg (star a ⬝ᵥ b)
    linarith
  rw [h.inner_sum, star_add_dotProduct, h.unit_a, h.inner_target_symm,
    show (2 : ℂ) + 2 * ((‖star a ⬝ᵥ b‖ : ℝ) : ℂ)
        = 2 * (1 + ((‖star a ⬝ᵥ b‖ : ℝ) : ℂ)) from by ring,
    div_mul_eq_mul_div, div_self (mul_ne_zero two_ne_zero hk)]

end IsTransportDatum

/-- **The transport carries `a` to `b`.**  Stated as a matrix identity so that
it composes: `rk1 a v = rk1 a a * rk1 a v` for a unit `a`. -/
theorem transportRot_mul_rk1 {a b : n → ℂ} (h : IsTransportDatum a b) (v : n → ℂ) :
    transportRot a b * rk1 a v = rk1 b v := by
  have ha : star a ⬝ᵥ a ≠ 0 := by rw [h.unit_a]; exact one_ne_zero
  have hstep1 : reflMat a * rk1 a v = -rk1 a v := reflMat_mul_rk1_self ha v
  have hstep2 : reflMat (a + transTarget a b) * rk1 a v
      = rk1 a v - rk1 (a + transTarget a b) v := by
    rw [reflMat_mul_rk1, h.sum_coeff, one_smul]
  have hstep3 : reflMat (a + transTarget a b) * (-rk1 a v) = rk1 (transTarget a b) v := by
    rw [Matrix.mul_neg, hstep2, rk1_add_left]
    abel
  rw [transportRot, Matrix.smul_mul, Matrix.mul_assoc, hstep1, hstep3, transTarget,
    rk1_smul_left, smul_smul, h.transPhase_mul_star, one_smul]

theorem transportRot_conjTranspose_mul_self {a b : n → ℂ} (h : IsTransportDatum a b) :
    (transportRot a b)ᴴ * transportRot a b = 1 := by
  have ha : star a ⬝ᵥ a ≠ 0 := by rw [h.unit_a]; exact one_ne_zero
  have hs := h.inner_sum_ne
  rw [transportRot, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    reflMat_conjTranspose, reflMat_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, h.star_transPhase_mul, one_smul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (reflMat (a + transTarget a b)), reflMat_mul_self hs,
    Matrix.one_mul, reflMat_mul_self ha]

theorem transportRot_mul_conjTranspose {a b : n → ℂ} (h : IsTransportDatum a b) :
    transportRot a b * (transportRot a b)ᴴ = 1 := by
  have ha : star a ⬝ᵥ a ≠ 0 := by rw [h.unit_a]; exact one_ne_zero
  have hs := h.inner_sum_ne
  rw [transportRot, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    reflMat_conjTranspose, reflMat_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, h.transPhase_mul_star, one_smul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (reflMat a), reflMat_mul_self ha, Matrix.one_mul,
    reflMat_mul_self hs]

/-! ### The two-step frame

One step is not enough: `transportRot p x` needs `pᴴx ≠ 0`, and `{pᴴx = 0}` is
a 3-sphere meeting both closed hemispheres.  Going through the normalised
midpoint costs one square root and buys the whole punctured sphere, because
the two inner products that must be nonzero are the same number. -/

/-- The length of `p + x`, for unit `p` and `x`. -/
def midNorm (p x : n → ℂ) : ℂ :=
  ((Real.sqrt (2 + 2 * (star p ⬝ᵥ x).re) : ℝ) : ℂ)

/-- The normalised midpoint of the geodesic from `p` to `x`. -/
def midVec (p x : n → ℂ) : n → ℂ := (midNorm p x)⁻¹ • (p + x)

/-- **The two-step frame rotation**: an explicit unitary carrying `p` to `x`,
continuous wherever `pᴴx ≠ -1`, i.e. on the whole sphere minus the antipode
of `p`. -/
def frameRot (p x : n → ℂ) : Matrix n n ℂ :=
  transportRot (midVec p x) x * transportRot p (midVec p x)

/-- The data making the two-step frame work: two unit vectors that are not
antipodal. -/
structure IsFrameDatum (p x : n → ℂ) : Prop where
  unit_p : star p ⬝ᵥ p = 1
  unit_x : star x ⬝ᵥ x = 1
  not_antipodal : star p ⬝ᵥ x ≠ -1

namespace IsFrameDatum

variable {p x : n → ℂ}

theorem sum_sq (h : IsFrameDatum p x) :
    star (p + x) ⬝ᵥ (p + x) = ((2 + 2 * (star p ⬝ᵥ x).re : ℝ) : ℂ) := by
  have hsym : star x ⬝ᵥ p = star (star p ⬝ᵥ x) := star_dotProduct_comm p x
  rw [star_add_dotProduct, star_dotProduct_add, star_dotProduct_add, h.unit_p,
    h.unit_x, hsym]
  have : (star p ⬝ᵥ x) + star (star p ⬝ᵥ x) = ((2 * (star p ⬝ᵥ x).re : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.add_conj]
  push_cast
  rw [show (1 : ℂ) + star p ⬝ᵥ x + (star (star p ⬝ᵥ x) + 1)
      = ((star p ⬝ᵥ x) + star (star p ⬝ᵥ x)) + 2 by ring, this]
  push_cast
  ring

/-- Positivity, and the exact point at which it fails: `2 + 2 Re(pᴴx)` is the
squared length of `p + x`, so it is nonnegative, and it vanishes only when
`x = -p`, i.e. only when `pᴴx = -1`. -/
theorem sum_sq_pos (h : IsFrameDatum p x) : 0 < 2 + 2 * (star p ⬝ᵥ x).re := by
  have hnn : 0 ≤ (star (p + x) ⬝ᵥ (p + x)).re := star_dotProduct_self_re_nonneg _
  rw [h.sum_sq, Complex.ofReal_re] at hnn
  rcases lt_or_eq_of_le hnn with hlt | heq
  · exact hlt
  · exfalso
    have hz : star (p + x) ⬝ᵥ (p + x) = 0 := by
      rw [h.sum_sq, ← heq]
      norm_num
    have hpx : p + x = 0 := eq_zero_of_star_dotProduct_self_eq_zero hz
    have hx : x = -p := by
      have := congrArg (fun w => w - p) hpx
      simpa [sub_eq_add_neg, add_comm] using this
    apply h.not_antipodal
    rw [hx]
    have : star p ⬝ᵥ (-p) = -(star p ⬝ᵥ p) := by
      rw [← neg_one_smul ℂ p, star_dotProduct_smul]
      ring
    rw [this, h.unit_p]

theorem midNorm_ne_zero (h : IsFrameDatum p x) : midNorm p x ≠ 0 := by
  have hpos := h.sum_sq_pos
  have : (0 : ℝ) < Real.sqrt (2 + 2 * (star p ⬝ᵥ x).re) := Real.sqrt_pos.mpr hpos
  simpa [midNorm] using ne_of_gt this

theorem midNorm_sq (h : IsFrameDatum p x) :
    midNorm p x * midNorm p x = star (p + x) ⬝ᵥ (p + x) := by
  rw [h.sum_sq, midNorm, ← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt h.sum_sq_pos)]

theorem star_midNorm (p x : n → ℂ) : star (midNorm p x) = midNorm p x := by
  simp [midNorm]

theorem unit_mid (h : IsFrameDatum p x) :
    star (midVec p x) ⬝ᵥ midVec p x = 1 := by
  have hm := h.midNorm_ne_zero
  rw [midVec, star_smul_dotProduct, star_dotProduct_smul, star_inv₀, star_midNorm,
    ← mul_assoc, ← mul_inv, h.midNorm_sq, inv_mul_cancel₀]
  rw [← h.midNorm_sq]
  exact mul_ne_zero hm hm

/-- The single scalar whose non-vanishing runs both steps. -/
theorem inner_p_mid (h : IsFrameDatum p x) :
    star p ⬝ᵥ midVec p x = (midNorm p x)⁻¹ * (1 + star p ⬝ᵥ x) := by
  rw [midVec, star_dotProduct_smul, star_dotProduct_add, h.unit_p]

theorem inner_mid_x (h : IsFrameDatum p x) :
    star (midVec p x) ⬝ᵥ x = (midNorm p x)⁻¹ * (1 + star p ⬝ᵥ x) := by
  rw [midVec, star_smul_dotProduct, star_inv₀, star_midNorm, star_add_dotProduct,
    h.unit_x]
  ring

theorem one_add_inner_ne (h : IsFrameDatum p x) : (1 : ℂ) + star p ⬝ᵥ x ≠ 0 := by
  intro hc
  apply h.not_antipodal
  linear_combination hc

theorem inner_p_mid_ne (h : IsFrameDatum p x) : star p ⬝ᵥ midVec p x ≠ 0 := by
  rw [h.inner_p_mid]
  exact mul_ne_zero (inv_ne_zero h.midNorm_ne_zero) h.one_add_inner_ne

theorem inner_mid_x_ne (h : IsFrameDatum p x) : star (midVec p x) ⬝ᵥ x ≠ 0 := by
  rw [h.inner_mid_x]
  exact mul_ne_zero (inv_ne_zero h.midNorm_ne_zero) h.one_add_inner_ne

theorem transportDatum_fst (h : IsFrameDatum p x) : IsTransportDatum p (midVec p x) :=
  ⟨h.unit_p, h.unit_mid, h.inner_p_mid_ne⟩

theorem transportDatum_snd (h : IsFrameDatum p x) : IsTransportDatum (midVec p x) x :=
  ⟨h.unit_mid, h.unit_x, h.inner_mid_x_ne⟩

end IsFrameDatum

/-- **The frame rotation carries `p` to `x`.** -/
theorem frameRot_mul_rk1 {p x : n → ℂ} (h : IsFrameDatum p x) (v : n → ℂ) :
    frameRot p x * rk1 p v = rk1 x v := by
  rw [frameRot, Matrix.mul_assoc, transportRot_mul_rk1 h.transportDatum_fst,
    transportRot_mul_rk1 h.transportDatum_snd]

theorem frameRot_conjTranspose_mul_self {p x : n → ℂ} (h : IsFrameDatum p x) :
    (frameRot p x)ᴴ * frameRot p x = 1 := by
  rw [frameRot, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc ((transportRot (midVec p x) x)ᴴ),
    transportRot_conjTranspose_mul_self h.transportDatum_snd, Matrix.one_mul,
    transportRot_conjTranspose_mul_self h.transportDatum_fst]

theorem frameRot_mul_conjTranspose {p x : n → ℂ} (h : IsFrameDatum p x) :
    frameRot p x * (frameRot p x)ᴴ = 1 := by
  rw [frameRot, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (transportRot p (midVec p x)),
    transportRot_mul_conjTranspose h.transportDatum_fst, Matrix.one_mul,
    transportRot_mul_conjTranspose h.transportDatum_snd]

/-! ### Continuity

Every ingredient is a rational expression in the entries, so continuity is
routine once the denominators are known to be nonzero.  The statements are
given over a parameter space on which the non-vanishing holds *everywhere*,
because that is how they are used: the hemispheres are subtypes cut out by
exactly that condition. -/

section Continuity

variable {X : Type*} [TopologicalSpace X]

theorem continuous_star_dotProduct {a b : X → n → ℂ} (ha : Continuous a)
    (hb : Continuous b) : Continuous fun t => star (a t) ⬝ᵥ b t := by
  show Continuous fun t => ∑ i, star (a t i) * b t i
  exact continuous_finsetSum _ fun i _ =>
    (((continuous_apply i).comp ha).star).mul ((continuous_apply i).comp hb)

theorem continuous_reflMat {v : X → n → ℂ} (hv : Continuous v)
    (hne : ∀ t, star (v t) ⬝ᵥ v t ≠ 0) : Continuous fun t => reflMat (v t) := by
  have h1 : Continuous fun t => (2 : ℂ) / (star (v t) ⬝ᵥ v t) :=
    continuous_const.div (continuous_star_dotProduct hv hv) hne
  exact continuous_const.sub (h1.smul (continuous_rk1 hv hv))

theorem continuous_transPhase {a b : X → n → ℂ} (ha : Continuous a) (hb : Continuous b)
    (hne : ∀ t, star (a t) ⬝ᵥ b t ≠ 0) :
    Continuous fun t => transPhase (a t) (b t) := by
  refine Continuous.div (continuous_star_dotProduct ha hb) ?_ ?_
  · exact Complex.continuous_ofReal.comp (continuous_star_dotProduct ha hb).norm
  · intro t
    simpa using hne t

theorem continuous_transTarget {a b : X → n → ℂ} (ha : Continuous a) (hb : Continuous b)
    (hne : ∀ t, star (a t) ⬝ᵥ b t ≠ 0) :
    Continuous fun t => transTarget (a t) (b t) :=
  Continuous.smul (continuous_transPhase ha hb hne).star hb

theorem continuous_transportRot {a b : X → n → ℂ} (ha : Continuous a) (hb : Continuous b)
    (hd : ∀ t, IsTransportDatum (a t) (b t)) :
    Continuous fun t => transportRot (a t) (b t) := by
  have hne : ∀ t, star (a t) ⬝ᵥ b t ≠ 0 := fun t => (hd t).inner_ne
  have haa : ∀ t, star (a t) ⬝ᵥ a t ≠ 0 := fun t => by
    rw [(hd t).unit_a]; exact one_ne_zero
  refine Continuous.smul (continuous_transPhase ha hb hne) (Continuous.mul ?_ ?_)
  · exact continuous_reflMat (ha.add (continuous_transTarget ha hb hne))
      fun t => (hd t).inner_sum_ne
  · exact continuous_reflMat ha haa

theorem continuous_midNorm {p x : X → n → ℂ} (hp : Continuous p) (hx : Continuous x) :
    Continuous fun t => midNorm (p t) (x t) :=
  Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
    (continuous_const.add (continuous_const.mul
      (Complex.continuous_re.comp (continuous_star_dotProduct hp hx)))))

theorem continuous_midVec {p x : X → n → ℂ} (hp : Continuous p) (hx : Continuous x)
    (hne : ∀ t, midNorm (p t) (x t) ≠ 0) :
    Continuous fun t => midVec (p t) (x t) :=
  Continuous.smul ((continuous_midNorm hp hx).inv₀ hne) (hp.add hx)

theorem continuous_frameRot {p x : X → n → ℂ} (hp : Continuous p) (hx : Continuous x)
    (hd : ∀ t, IsFrameDatum (p t) (x t)) :
    Continuous fun t => frameRot (p t) (x t) := by
  have hmid : Continuous fun t => midVec (p t) (x t) :=
    continuous_midVec hp hx fun t => (hd t).midNorm_ne_zero
  exact Continuous.mul (continuous_transportRot hmid hx fun t => (hd t).transportDatum_snd)
    (continuous_transportRot hp hmid fun t => (hd t).transportDatum_fst)

end Continuity

/-! ### The two hemisphere frames and the seam generator

`frameRot p ·` is defined on the whole sphere minus `-p`, so it trivialises
the tautological complement over the closed hemisphere around `p`; the same
formula based at `-p` does the other one, corrected by the reflection that
carries `p` to `-p`, so that both satisfy the *same* identity
`σ * rk1 p v = rk1 x v`.  Their seam discrepancy fixes `p`, which is exactly
the statement that it is `diag(u, 1)`. -/

section Seam

variable {p : n → ℂ}

theorem star_neg_dotProduct (a b : n → ℂ) : star (-a) ⬝ᵥ b = -(star a ⬝ᵥ b) := by
  rw [star_neg, neg_dotProduct]

theorem star_dotProduct_neg (a b : n → ℂ) : star a ⬝ᵥ (-b) = -(star a ⬝ᵥ b) :=
  dotProduct_neg _ _

/-- The southern frame datum: `-p` is a unit vector, and `x` is not its
antipode exactly when `pᴴ x ≠ 1`. -/
theorem isFrameDatum_neg {x : n → ℂ} (hp : star p ⬝ᵥ p = 1) (hx : star x ⬝ᵥ x = 1)
    (hne : star p ⬝ᵥ x ≠ 1) : IsFrameDatum (-p) x where
  unit_p := by rw [star_neg_dotProduct, star_dotProduct_neg, neg_neg, hp]
  unit_x := hx
  not_antipodal := by
    rw [star_neg_dotProduct]
    intro hc
    exact hne (by linear_combination -hc)

/-- The northern hemisphere frame. -/
def frameNorth (p x : n → ℂ) : Matrix n n ℂ := frameRot p x

/-- The southern hemisphere frame: the same construction based at the
antipode, corrected by the reflection carrying `p` to `-p`, so that it obeys
the same transport identity. -/
def frameSouth (p x : n → ℂ) : Matrix n n ℂ := frameRot (-p) x * reflMat p

/-- **The seam generator.**  On the equator both frames are defined, and their
discrepancy is a unitary fixing `p`. -/
def seamGen (p x : n → ℂ) : Matrix n n ℂ := (frameNorth p x)ᴴ * frameSouth p x

theorem frameNorth_mul_rk1 {x : n → ℂ} (h : IsFrameDatum p x) (v : n → ℂ) :
    frameNorth p x * rk1 p v = rk1 x v := frameRot_mul_rk1 h v

theorem frameSouth_mul_rk1 {x : n → ℂ} (hp : star p ⬝ᵥ p = 1)
    (h : IsFrameDatum (-p) x) (v : n → ℂ) : frameSouth p x * rk1 p v = rk1 x v := by
  have hpne : star p ⬝ᵥ p ≠ 0 := by rw [hp]; exact one_ne_zero
  have hneg : reflMat p * rk1 p v = rk1 (-p) v := by
    rw [reflMat_mul_rk1_self hpne, rk1_neg_left]
  rw [frameSouth, Matrix.mul_assoc, hneg, frameRot_mul_rk1 h v]

theorem frameNorth_conjTranspose_mul_self {x : n → ℂ} (h : IsFrameDatum p x) :
    (frameNorth p x)ᴴ * frameNorth p x = 1 := frameRot_conjTranspose_mul_self h

theorem frameNorth_mul_conjTranspose {x : n → ℂ} (h : IsFrameDatum p x) :
    frameNorth p x * (frameNorth p x)ᴴ = 1 := frameRot_mul_conjTranspose h

theorem frameSouth_conjTranspose_mul_self {x : n → ℂ} (hp : star p ⬝ᵥ p = 1)
    (h : IsFrameDatum (-p) x) : (frameSouth p x)ᴴ * frameSouth p x = 1 := by
  have hpne : star p ⬝ᵥ p ≠ 0 := by rw [hp]; exact one_ne_zero
  rw [frameSouth, Matrix.conjTranspose_mul, reflMat_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc ((frameRot (-p) x)ᴴ), frameRot_conjTranspose_mul_self h,
    Matrix.one_mul, reflMat_mul_self hpne]

theorem frameSouth_mul_conjTranspose {x : n → ℂ} (hp : star p ⬝ᵥ p = 1)
    (h : IsFrameDatum (-p) x) : frameSouth p x * (frameSouth p x)ᴴ = 1 := by
  have hpne : star p ⬝ᵥ p ≠ 0 := by rw [hp]; exact one_ne_zero
  rw [frameSouth, Matrix.conjTranspose_mul, reflMat_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (reflMat p), reflMat_mul_self hpne, Matrix.one_mul,
    frameRot_mul_conjTranspose h]

/-- **The seam generator fixes `p`.**  This is the statement that `seamGen` is
`diag(u, 1)` for a unitary `u` of the orthogonal complement, expressed without
any submatrix surgery. -/
theorem seamGen_mul_rk1 {x : n → ℂ} (hp : star p ⬝ᵥ p = 1) (hN : IsFrameDatum p x)
    (hS : IsFrameDatum (-p) x) (v : n → ℂ) : seamGen p x * rk1 p v = rk1 p v := by
  have hkey : (frameNorth p x)ᴴ * rk1 x v = rk1 p v := by
    conv_lhs => rw [← frameNorth_mul_rk1 hN v]
    rw [← Matrix.mul_assoc, frameNorth_conjTranspose_mul_self hN, Matrix.one_mul]
  rw [seamGen, Matrix.mul_assoc, frameSouth_mul_rk1 hp hS v, hkey]

theorem seamGen_conjTranspose_mul_self {x : n → ℂ} (hp : star p ⬝ᵥ p = 1)
    (hN : IsFrameDatum p x) (hS : IsFrameDatum (-p) x) :
    (seamGen p x)ᴴ * seamGen p x = 1 := by
  rw [seamGen, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc (frameNorth p x),
    frameNorth_mul_conjTranspose hN, Matrix.one_mul,
    frameSouth_conjTranspose_mul_self hp hS]

theorem seamGen_mul_conjTranspose {x : n → ℂ} (hp : star p ⬝ᵥ p = 1)
    (hN : IsFrameDatum p x) (hS : IsFrameDatum (-p) x) :
    seamGen p x * (seamGen p x)ᴴ = 1 := by
  rw [seamGen, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc (frameSouth p x),
    frameSouth_mul_conjTranspose hp hS, Matrix.one_mul,
    frameNorth_conjTranspose_mul_self hN]

/-- **A frame of the tautological complement.**  A unitary obeying the
transport identity conjugates the complement of `p pᴴ` onto the complement of
`x xᴴ`; over `S⁵ ⊆ ℂ³` with `p = e₃` the right-hand side is exactly
`STW59.Fproj` read pointwise. -/
theorem conj_one_sub_rk1 {σ : Matrix n n ℂ} {x : n → ℂ}
    (hu : σ * σᴴ = 1) (hv : ∀ v, σ * rk1 p v = rk1 x v) :
    σ * (1 - rk1 p p) * σᴴ = 1 - rk1 x x := by
  have h3 : rk1 x p * σᴴ = rk1 x x := by
    have h2 := congrArg Matrix.conjTranspose (hv x)
    rwa [Matrix.conjTranspose_mul, rk1_conjTranspose, rk1_conjTranspose] at h2
  rw [mul_sub, Matrix.mul_one, sub_mul, hu, hv p, h3]

end Seam

end Frames

end

end LIX
end GroupApproximation
