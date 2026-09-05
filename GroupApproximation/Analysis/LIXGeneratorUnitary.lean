import GroupApproximation.Analysis.LIXClutching

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
      | linear_combination -hn

theorem su2_mul_conjTranspose {α β : ℂ} (h : Complex.normSq α + Complex.normSq β = 1) :
    su2 α β * (su2 α β)ᴴ = 1 := by
  have hn := su2_norm_relation h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2, su2_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    first
      | ring1
      | linear_combination hn
      | linear_combination -hn

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
    rw [← hnz, ← hnw]
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

end

end LIX
end GroupApproximation
