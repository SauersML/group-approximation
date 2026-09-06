import GroupApproximation.CharClass.BundleLineTriv

/-!
# Complex vector bundles in the projection model, XXVII: an intertwiner becomes
an isomorphism, at rank one

At general rank, turning an invertible intertwiner into a `BundleIso` needs a
continuous polar decomposition, and there is none in the tree.  **At rank one it
needs no square root of a matrix at all**, only a square root of a positive
real, which is continuous:

    w y = (A y * p y) / ‖A y * p y‖    with  ‖·‖ the Hilbert-Schmidt norm.

For a rank-one `p y = u uᴴ` the matrix `A y * p y` is `(A u) uᴴ`, so
`wᴴ w = p y` and `w wᴴ` is the line spanned by `A u`, which is `q y` as soon as
`A` carries the fibre of `p` into the fibre of `q` without killing it.  No
invertibility of `A` is needed, only that it does not kill the fibre; that is the
same weakening `conjNormalize_mem_projFibreSet'` makes.

This is `lineHom`'s normalisation with the column replaced by `A` applied to the
fibre.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

/-! ### The rank-one scalar identity -/

section Scalar

variable {ι : Type} [Fintype ι]

theorem sum_star_mul_self_eq_eucNormSq (v : ι → ℂ) :
    ∑ k, star (v k) * v k = ((eucNormSq v : ℝ) : ℂ) := by
  rw [eucNormSq_def, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun k _ => star_mul_self_eq_normSq (v k)

omit [Fintype ι] in
theorem conjTranspose_vecMulVec (x y : ι → ℂ) :
    (Matrix.vecMulVec x y)ᴴ = Matrix.vecMulVec (star y) (star x) := by
  ext i j
  simp [Matrix.vecMulVec_apply, mul_comm]

omit [Fintype ι] in
theorem vecMulVec_smul_right (x y : ι → ℂ) (c : ℂ) :
    Matrix.vecMulVec x (c • y) = c • Matrix.vecMulVec x y := by
  ext i j
  simp [Matrix.vecMulVec_apply, mul_left_comm]

/-- **The rank-one identity.**  `(A P)ᴴ (A P) = ‖A u‖² P` when `P = u uᴴ`. -/
theorem conjTranspose_mul_self_rankOneProj (a : Matrix ι ι ℂ) (u : ι → ℂ) :
    (a * rankOneProj u)ᴴ * (a * rankOneProj u)
      = ((eucNormSq (a *ᵥ u) : ℝ) : ℂ) • rankOneProj u := by
  rw [mul_rankOneProj, conjTranspose_vecMulVec, star_star,
    Matrix.vecMulVec_mul_vecMulVec]
  have hdot : (star (a *ᵥ u) ⬝ᵥ (a *ᵥ u)) = ((eucNormSq (a *ᵥ u) : ℝ) : ℂ) :=
    sum_star_mul_self_eq_eucNormSq (a *ᵥ u)
  rw [hdot, vecMulVec_smul_right]
  rfl

theorem trace_conjTranspose_mul_self_rankOneProj (a : Matrix ι ι ℂ) {u : ι → ℂ}
    (hu : u ∈ unitVectors ι) :
    ((a * rankOneProj u)ᴴ * (a * rankOneProj u)).trace
      = ((eucNormSq (a *ᵥ u) : ℝ) : ℂ) := by
  rw [conjTranspose_mul_self_rankOneProj, Matrix.trace_smul, trace_rankOneProj hu,
    smul_eq_mul, mul_one]

/-- `(A P)(A P)ᴴ` is the rank-one projection on `A u`. -/
theorem mul_rankOneProj_mul_conjTranspose (a : Matrix ι ι ℂ) {u : ι → ℂ}
    (hu : u ∈ unitVectors ι) :
    (a * rankOneProj u) * (a * rankOneProj u)ᴴ = rankOneProj (a *ᵥ u) := by
  have hH : (rankOneProj u)ᴴ = rankOneProj u :=
    conjTranspose_eq_of_isStarProjection (isStarProjection_rankOneProj hu)
  have hid : rankOneProj u * rankOneProj u = rankOneProj u :=
    (isStarProjection_rankOneProj hu).isIdempotentElem.eq
  calc (a * rankOneProj u) * (a * rankOneProj u)ᴴ
      = a * (rankOneProj u * rankOneProj u) * aᴴ := by
        rw [Matrix.conjTranspose_mul, hH]
        simp only [Matrix.mul_assoc]
    _ = a * rankOneProj u * aᴴ := by rw [hid]
    _ = rankOneProj (a *ᵥ u) := conj_rankOneProj a u

end Scalar

/-! ### Two real-scalar facts, the only square root anywhere -/

theorem inv_sqrt_mul_inv_sqrt {c : ℝ} (hc : 0 < c) :
    (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ = c⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt hc.le]

theorem star_ofReal_inv (s : ℝ) : star (((s : ℝ) : ℂ)⁻¹) = ((s : ℝ) : ℂ)⁻¹ := by
  rw [← Complex.ofReal_inv]
  exact Complex.conj_ofReal _

/-- The scalar that normalises: `(√c)⁻¹` squared against `c` is one. -/
theorem inv_sqrt_sq_smul {c : ℝ} (hc : 0 < c) :
    star (((Real.sqrt c : ℝ) : ℂ)⁻¹) * ((Real.sqrt c : ℝ) : ℂ)⁻¹ * ((c : ℝ) : ℂ) = 1 := by
  rw [star_ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    inv_sqrt_mul_inv_sqrt hc, inv_mul_cancel₀ hc.ne', Complex.ofReal_one]

theorem inv_sqrt_sq_eq {c : ℝ} (hc : 0 < c) :
    ((Real.sqrt c : ℝ) : ℂ)⁻¹ * star (((Real.sqrt c : ℝ) : ℂ)⁻¹) = ((c : ℝ) : ℂ)⁻¹ := by
  rw [star_ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_sqrt_mul_inv_sqrt hc,
    Complex.ofReal_inv]

/-! ### The isomorphism -/

section LineIntert

variable {Y : Type} [TopologicalSpace Y] {ι : Type} [Fintype ι]

/-- The Hilbert-Schmidt norm of `A y * p y`, a continuous real scalar. -/
noncomputable def intertScale (A : Y → Matrix ι ι ℂ) (p : Bundle Y ι) (y : Y) : ℝ :=
  Real.sqrt ((((A y * p y)ᴴ * (A y * p y)).trace).re)

/-- The normalised intertwiner. -/
noncomputable def lineIntertHom (A : Y → Matrix ι ι ℂ) (p : Bundle Y ι) (y : Y) :
    Matrix ι ι ℂ :=
  ((intertScale A p y : ℝ) : ℂ)⁻¹ • (A y * p y)

variable {A : Y → Matrix ι ι ℂ} {p q : Bundle Y ι}

theorem intertScale_eq (y : Y) {u : ι → ℂ}
    (hu : u ∈ unitVectors ι) (hpu : p y = rankOneProj u) :
    intertScale A p y = Real.sqrt (eucNormSq (A y *ᵥ u)) := by
  rw [intertScale, hpu, trace_conjTranspose_mul_self_rankOneProj _ hu, Complex.ofReal_re]

theorem intertScale_pos (y : Y) {u : ι → ℂ}
    (hu : u ∈ unitVectors ι) (hpu : p y = rankOneProj u) (hne : A y *ᵥ u ≠ 0) :
    0 < intertScale A p y := by
  rw [intertScale_eq y hu hpu]
  exact Real.sqrt_pos.mpr (eucNormSq_pos hne)

theorem lineIntertHom_conjTranspose_mul (y : Y) {u : ι → ℂ}
    (hu : u ∈ unitVectors ι) (hpu : p y = rankOneProj u) (hne : A y *ᵥ u ≠ 0) :
    (lineIntertHom A p y)ᴴ * lineIntertHom A p y = p y := by
  have hpos : (0 : ℝ) < eucNormSq (A y *ᵥ u) := eucNormSq_pos hne
  have hs : intertScale A p y = Real.sqrt (eucNormSq (A y *ᵥ u)) := intertScale_eq y hu hpu
  rw [lineIntertHom, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hpu, conjTranspose_mul_self_rankOneProj, smul_smul, hs,
    inv_sqrt_sq_smul hpos, one_smul]

theorem lineIntertHom_mul_conjTranspose (y : Y) {u : ι → ℂ}
    (hu : u ∈ unitVectors ι) (hpu : p y = rankOneProj u) (hne : A y *ᵥ u ≠ 0)
    (hq : IsStarProjection (q y)) (hqt : (q y).trace = 1)
    (hfix : q y *ᵥ (A y *ᵥ u) = A y *ᵥ u) :
    lineIntertHom A p y * (lineIntertHom A p y)ᴴ = q y := by
  have hpos : (0 : ℝ) < eucNormSq (A y *ᵥ u) := eucNormSq_pos hne
  have hs : intertScale A p y = Real.sqrt (eucNormSq (A y *ᵥ u)) := intertScale_eq y hu hpu
  have hline : lineOf (A y *ᵥ u) = q y := lineOf_eq_of_mem_fibre hq hqt hne hfix
  rw [lineIntertHom, Matrix.smul_mul, Matrix.conjTranspose_smul, Matrix.mul_smul,
    smul_smul, hpu, mul_rankOneProj_mul_conjTranspose _ hu, hs, inv_sqrt_sq_eq hpos,
    ← lineOf_def, hline]

theorem continuous_intertScale (hA : Continuous A) (p : Bundle Y ι) :
    Continuous (intertScale A p) :=
  Real.continuous_sqrt.comp (Complex.continuous_re.comp
    (((hA.matrix_mul p.continuous).matrix_conjTranspose.matrix_mul
      (hA.matrix_mul p.continuous)).matrix_trace))

/-- **An intertwiner of line bundles is an isomorphism.**

`A` need not be invertible and need not be unitary; it need only carry the fibre
of `p` into the fibre of `q` without killing it.  The implementer is `A * p`
normalised by its Hilbert-Schmidt norm, so the only square root taken anywhere
is that of a positive real, which is continuous.  At general rank the same
statement needs a continuous polar decomposition and is not available. -/
noncomputable def lineIntertIso (A : Y → Matrix ι ι ℂ) (hA : Continuous A)
    (p q : Bundle Y ι) (hp : ∀ y, (p y).trace = 1) (hq : ∀ y, (q y).trace = 1)
    (hfix : ∀ (y : Y) (v : ι → ℂ), p y *ᵥ v = v → q y *ᵥ (A y *ᵥ v) = A y *ᵥ v)
    (hne : ∀ (y : Y) (v : ι → ℂ), p y *ᵥ v = v → v ≠ 0 → A y *ᵥ v ≠ 0) :
    BundleIso p q where
  hom := lineIntertHom A p
  continuous_hom := by
    have hpos : ∀ y, 0 < intertScale A p y := by
      intro y
      obtain ⟨u, hu, hpu⟩ := eq_rankOneProj_of_trace_one (p.isStarProjection y) (hp y)
      exact intertScale_pos y hu hpu
        (hne y u (by rw [hpu]; exact rankOneProj_mulVec_self hu)
          (ne_zero_of_eucNormSq_eq_one hu))
    have hs : Continuous fun y => ((intertScale A p y : ℝ) : ℂ)⁻¹ := by
      refine (Complex.continuous_ofReal.comp (continuous_intertScale hA p)).inv₀ fun y => ?_
      exact Complex.ofReal_ne_zero.mpr (hpos y).ne'
    exact hs.smul (hA.matrix_mul p.continuous)
  conjTranspose_mul y := by
    obtain ⟨u, hu, hpu⟩ := eq_rankOneProj_of_trace_one (p.isStarProjection y) (hp y)
    exact lineIntertHom_conjTranspose_mul y hu hpu
      (hne y u (by rw [hpu]; exact rankOneProj_mulVec_self hu)
        (ne_zero_of_eucNormSq_eq_one hu))
  mul_conjTranspose y := by
    obtain ⟨u, hu, hpu⟩ := eq_rankOneProj_of_trace_one (p.isStarProjection y) (hp y)
    have hfibre : p y *ᵥ u = u := by rw [hpu]; exact rankOneProj_mulVec_self hu
    exact lineIntertHom_mul_conjTranspose y hu hpu
      (hne y u hfibre (ne_zero_of_eucNormSq_eq_one hu))
      (q.isStarProjection y) (hq y) (hfix y u hfibre)

theorem lineIntertIso_hom (A : Y → Matrix ι ι ℂ) (hA : Continuous A) (p q : Bundle Y ι)
    (hp : ∀ y, (p y).trace = 1) (hq : ∀ y, (q y).trace = 1)
    (hfix : ∀ (y : Y) (v : ι → ℂ), p y *ᵥ v = v → q y *ᵥ (A y *ᵥ v) = A y *ᵥ v)
    (hne : ∀ (y : Y) (v : ι → ℂ), p y *ᵥ v = v → v ≠ 0 → A y *ᵥ v ≠ 0) (y : Y) :
    (lineIntertIso A hA p q hp hq hfix hne).hom y
      = ((intertScale A p y : ℝ) : ℂ)⁻¹ • (A y * p y) := rfl

end LineIntert

end Bundle

end CharClass
end GroupApproximation
