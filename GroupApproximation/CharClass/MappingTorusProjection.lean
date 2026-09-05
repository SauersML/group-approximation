import Mathlib

/-!
# The mapping torus of a corner unitary, in the projection model

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step B).

A complex vector bundle over a compact Hausdorff `M` **is** a continuous
projection-valued map `M → Matrix n n ℂ`.  Given such a `V` and a unitary `g` of the
corner `V M_n(C(M)) V`, the manuscript
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`,
proof of Lemma 2, equation (2.9)) forms the **mapping torus**

```text
W_g = (V × [0,1]) / ((v, 1) ∼ (g⁻¹ v, 0))  →  S¹ × M .
```

This file builds `W_g` **without any quotient**: as an explicit projection-valued map on
`S¹ × M`, where `S¹` carries its two coordinates `(y, t)` with `y² + t² = 1`, is split
into two closed half-discs by the height `t`, and is glued along the two-point equator
`{y = ±1}` by the transition matrix `G` at `y = 1` and by `1` at `y = -1`.

## Why this presentation, and not a Whitehead path

The route through a Whitehead path `h : [0,1] → U(2n)` from `1` to `diag(G, Gᴴ)` does give
a loop of projections `t ↦ h t (V ⊕ 0) (h t)ᴴ` — one checks `h 1` commutes with `V ⊕ 0`.
But that loop only descends to `S¹` through the quotient `[0,1]/(0 ∼ 1)`, and **no**
reparametrisation turns it into a polynomial in `(cos θ, sin θ)`: the entries are degree-4
monomials in `(cos(θ/4), sin(θ/4))`, and running the rotation over the whole circle
returns `h` to `1`, which *untwists* the bundle (a loop `h` in `U(2n)` trivialises
`h (V ⊕ 0) hᴴ`).  Clutching two half-circle families along the two-point equator avoids the
quotient entirely and, as a bonus, gives the restriction to the north-pole slice **on the
nose** (`mappingTorus_north`), not merely up to Murray--von Neumann equivalence.

## Main results

* `cornerExtend`, `isCornerUnitary_cornerExtend` — a unitary `g` of the corner `V M_n V`
  extends by `1 - V` to a unitary `G` of `M_n` commuting with `V`.
* `mtProj` — the clutched projection of the two half-circle families, a self-adjoint
  idempotent (`mtProj_isStarProjection`).
* `mappingTorus` — the bundle `W_g`, a continuous projection-valued map on `Z × M` for any
  circle chart `Z` (`mappingTorus_isStarProjection`, `mappingTorus_continuous`).
* `mappingTorus_north` — `W_g` on the north-pole slice is `V ⊕ 0`, on the nose.
* `trace_mappingTorus` — `rank W_g = rank V`, as an identity of traces.
* `sphereOne` with `isCircleChart_sphereOne` — the concrete circle recorded by this lane:
  the unit sphere of `EuclideanSpace ℝ (Fin 2)`, matching the repo's `sphereFour` and
  `sphereFive` convention.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix

/-! ## 1. Extending a corner unitary -/

section CornerUnitary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A **unitary of `M_n(ℂ)` commuting with the projection `V`**: the shape of the
transition matrix the mapping torus consumes.  `cornerExtend` produces one from a unitary
of the corner `V M_n(ℂ) V`. -/
structure IsCornerUnitary (V G : Matrix n n ℂ) : Prop where
  /-- `V` is a self-adjoint idempotent. -/
  proj : IsStarProjection V
  /-- `G` is an isometry. -/
  star_mul_self : Gᴴ * G = 1
  /-- `G` is a coisometry. -/
  mul_star_self : G * Gᴴ = 1
  /-- `G` preserves the range of `V`. -/
  commutes : G * V = V * G

/-- The unitary of `M_n(ℂ)` obtained from a unitary `g` of the corner `V M_n(ℂ) V` by
letting it act as the identity on the complementary range. -/
def cornerExtend (V g : Matrix n n ℂ) : Matrix n n ℂ := g + (1 - V)

variable {V g : Matrix n n ℂ}

theorem proj_conjTranspose (hV : IsStarProjection V) : Vᴴ = V := by
  have h : star V = V := hV.isSelfAdjoint.star_eq
  rwa [Matrix.star_eq_conjTranspose] at h

theorem cornerExtend_conjTranspose (hV : IsStarProjection V) :
    (cornerExtend V g)ᴴ = cornerExtend V gᴴ := by
  rw [cornerExtend, cornerExtend, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, proj_conjTranspose hV]

private theorem compl_mul (hVg : V * g = g) : (1 - V) * g = 0 := by
  rw [sub_mul, one_mul, hVg, sub_self]

private theorem mul_compl (hgV : g * V = g) : g * (1 - V) = 0 := by
  rw [mul_sub, mul_one, hgV, sub_self]

private theorem compl_idem (hV : IsStarProjection V) : (1 - V) * (1 - V) = 1 - V := by
  have hVV : V * V = V := hV.isIdempotentElem.eq
  rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hVV]
  abel

/-- **The extension is an isometry.** -/
theorem cornerExtend_star_mul_self (hV : IsStarProjection V) (hVg : V * g = g)
    (hgg : gᴴ * g = V) : (cornerExtend V g)ᴴ * (cornerExtend V g) = 1 := by
  have hgcV : gᴴ * V = gᴴ := by
    have h := congrArg Matrix.conjTranspose hVg
    rw [Matrix.conjTranspose_mul, proj_conjTranspose hV] at h
    exact h
  rw [cornerExtend_conjTranspose hV, cornerExtend, cornerExtend, add_mul, mul_add, mul_add,
    hgg, mul_compl hgcV, compl_mul hVg, compl_idem hV]
  abel

/-- **The extension is a coisometry.** -/
theorem cornerExtend_mul_star_self (hV : IsStarProjection V) (hgV : g * V = g)
    (hgg : g * gᴴ = V) : (cornerExtend V g) * (cornerExtend V g)ᴴ = 1 := by
  have hVgc : V * gᴴ = gᴴ := by
    have h := congrArg Matrix.conjTranspose hgV
    rw [Matrix.conjTranspose_mul, proj_conjTranspose hV] at h
    exact h
  rw [cornerExtend_conjTranspose hV, cornerExtend, cornerExtend, add_mul, mul_add, mul_add,
    hgg, mul_compl hgV, compl_mul hVgc, compl_idem hV]
  abel

theorem cornerExtend_mul_proj (hV : IsStarProjection V) (hgV : g * V = g) :
    cornerExtend V g * V = g := by
  have hVV : V * V = V := hV.isIdempotentElem.eq
  rw [cornerExtend, add_mul, sub_mul, one_mul, hVV, hgV, sub_self, add_zero]

theorem proj_mul_cornerExtend (hV : IsStarProjection V) (hVg : V * g = g) :
    V * cornerExtend V g = g := by
  have hVV : V * V = V := hV.isIdempotentElem.eq
  rw [cornerExtend, mul_add, mul_sub, mul_one, hVV, hVg, sub_self, add_zero]

/-- **The extension of a corner unitary is a unitary commuting with `V`.**  This is the
input Step B consumes, produced from the Murray--von Neumann data of Step A. -/
theorem isCornerUnitary_cornerExtend (hV : IsStarProjection V) (hgV : g * V = g)
    (hVg : V * g = g) (hgg : gᴴ * g = V) (hgg' : g * gᴴ = V) :
    IsCornerUnitary V (cornerExtend V g) where
  proj := hV
  star_mul_self := cornerExtend_star_mul_self hV hVg hgg
  mul_star_self := cornerExtend_mul_star_self hV hgV hgg'
  commutes := by rw [cornerExtend_mul_proj hV hgV, proj_mul_cornerExtend hV hVg]

theorem IsCornerUnitary.conjTranspose_commutes {G : Matrix n n ℂ} (h : IsCornerUnitary V G) :
    Gᴴ * V = V * Gᴴ := by
  have hc := congrArg Matrix.conjTranspose h.commutes
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, proj_conjTranspose h.proj] at hc
  exact hc.symm

end CornerUnitary

/-! ## 2. The clutched projection over the pair of half-circles -/

section Clutch

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The self-adjoint **symmetry** whose `+1`-eigenspace is the clutched family: when
`fᴴ f = f fᴴ = (1 - t²) • 1` its square is `1`. -/
def mtSym (t : ℝ) (f : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks ((t : ℂ) • 1) fᴴ f ((-(t : ℂ)) • 1)

/-- The **clutched projection**: two trivial rank-`n` families over the two closed
half-circles, glued along the equator by `f/‖y‖`. -/
def mtProj (t : ℝ) (f : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  (2⁻¹ : ℂ) • (1 + mtSym t f)

private theorem one_eq_fromBlocks :
    (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ)
      = Matrix.fromBlocks (1 : Matrix n n ℂ) 0 0 (1 : Matrix n n ℂ) :=
  Matrix.fromBlocks_one.symm

theorem mtSym_conjTranspose (t : ℝ) (f : Matrix n n ℂ) : (mtSym t f)ᴴ = mtSym t f := by
  rw [mtSym, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  congr 1 <;> simp [Complex.star_def, Complex.conj_ofReal]

/-- The clutching identity: with `‖y‖² = 1 - t²` the symmetry squares to `1`. -/
theorem mtSym_mul_self {t : ℝ} {f : Matrix n n ℂ}
    (h₁ : fᴴ * f = ((1 - t ^ 2 : ℝ) : ℂ) • 1) (h₂ : f * fᴴ = ((1 - t ^ 2 : ℝ) : ℂ) • 1) :
    mtSym t f * mtSym t f = 1 := by
  have hsc : ((t : ℂ) * (t : ℂ)) + ((1 - t ^ 2 : ℝ) : ℂ) = 1 := by push_cast; ring
  rw [mtSym, Matrix.fromBlocks_multiply, one_eq_fromBlocks]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, h₁, ← add_smul, hsc,
      one_smul]
  · rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, ← add_smul,
      add_neg_cancel, zero_smul]
  · rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, ← add_smul,
      add_neg_cancel, zero_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, h₂, add_comm,
      ← add_smul]
    rw [show ((1 - t ^ 2 : ℝ) : ℂ) + (-(t : ℂ)) * (-(t : ℂ)) = 1 by push_cast; ring,
      one_smul]

theorem mtProj_conjTranspose (t : ℝ) (f : Matrix n n ℂ) : (mtProj t f)ᴴ = mtProj t f := by
  rw [mtProj, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    mtSym_conjTranspose, Complex.star_def]
  norm_num

theorem mtProj_mul_self {t : ℝ} {f : Matrix n n ℂ}
    (h₁ : fᴴ * f = ((1 - t ^ 2 : ℝ) : ℂ) • 1) (h₂ : f * fᴴ = ((1 - t ^ 2 : ℝ) : ℂ) • 1) :
    mtProj t f * mtProj t f = mtProj t f := by
  have hsq := mtSym_mul_self h₁ h₂
  have hexp : (1 + mtSym t f) * (1 + mtSym t f) = (2 : ℂ) • (1 + mtSym t f) := by
    rw [add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hsq,
      two_smul]
    abel
  rw [mtProj, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hexp, smul_smul]
  norm_num

theorem mtProj_isStarProjection {t : ℝ} {f : Matrix n n ℂ}
    (h₁ : fᴴ * f = ((1 - t ^ 2 : ℝ) : ℂ) • 1) (h₂ : f * fᴴ = ((1 - t ^ 2 : ℝ) : ℂ) • 1) :
    IsStarProjection (mtProj t f) where
  isIdempotentElem := mtProj_mul_self h₁ h₂
  isSelfAdjoint := by
    have : star (mtProj t f) = mtProj t f := by
      rw [Matrix.star_eq_conjTranspose, mtProj_conjTranspose]
    exact this

/-- The clutched projection in block normal form: the shape every computation below uses. -/
theorem mtProj_eq (t : ℝ) (f : Matrix n n ℂ) :
    mtProj t f = Matrix.fromBlocks ((((1 + t) / 2 : ℝ) : ℂ) • 1) ((2⁻¹ : ℂ) • fᴴ)
      ((2⁻¹ : ℂ) • f) ((((1 - t) / 2 : ℝ) : ℂ) • 1) := by
  rw [mtProj, mtSym, one_eq_fromBlocks, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · rw [show ((1 : Matrix n n ℂ) + (t : ℂ) • 1) = ((1 + t : ℂ)) • (1 : Matrix n n ℂ) by
      rw [add_smul, one_smul], smul_smul]
    congr 1
    push_cast
    ring
  · rw [zero_add]
  · rw [add_zero]
  · rw [show ((1 : Matrix n n ℂ) + (-(t : ℂ)) • 1) = ((1 - t : ℂ)) • (1 : Matrix n n ℂ) by
      rw [sub_eq_add_neg, add_smul, one_smul, neg_smul], smul_smul]
    congr 1
    push_cast
    ring

end Clutch

/-! ## 3. The transition matrix along the circle -/

section Transition

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The transition matrix of the mapping torus as a function of the horizontal coordinate
`y`: `G` scaled by `y` on the right half of the circle, the identity scaled by `-y` on the
left half.  Both branches vanish at `y = 0`, so this is continuous, and its modulus is
`|y| = √(1 - t²)`, which is exactly the clutching normalisation. -/
def mtTrans (G : Matrix n n ℂ) (y : ℝ) : Matrix n n ℂ :=
  if 0 ≤ y then ((y : ℝ) : ℂ) • G else ((-y : ℝ) : ℂ) • 1

theorem mtTrans_conjTranspose (G : Matrix n n ℂ) (y : ℝ) :
    (mtTrans G y)ᴴ = mtTrans Gᴴ y := by
  unfold mtTrans
  split_ifs with h
  · rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]

theorem mtTrans_star_mul_self {V G : Matrix n n ℂ} (h : IsCornerUnitary V G) {y t : ℝ}
    (hyt : y ^ 2 + t ^ 2 = 1) :
    (mtTrans G y)ᴴ * mtTrans G y = ((1 - t ^ 2 : ℝ) : ℂ) • 1 := by
  have hy : (1 - t ^ 2 : ℝ) = y ^ 2 := by linarith
  rw [mtTrans_conjTranspose, hy]
  unfold mtTrans
  split_ifs with hpos
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h.star_mul_self]
    congr 1
    push_cast
    ring
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    congr 1
    push_cast
    ring

theorem mtTrans_mul_star_self {V G : Matrix n n ℂ} (h : IsCornerUnitary V G) {y t : ℝ}
    (hyt : y ^ 2 + t ^ 2 = 1) :
    mtTrans G y * (mtTrans G y)ᴴ = ((1 - t ^ 2 : ℝ) : ℂ) • 1 := by
  have hy : (1 - t ^ 2 : ℝ) = y ^ 2 := by linarith
  rw [mtTrans_conjTranspose, hy]
  unfold mtTrans
  split_ifs with hpos
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h.mul_star_self]
    congr 1
    push_cast
    ring
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    congr 1
    push_cast
    ring

theorem mtTrans_commutes {V G : Matrix n n ℂ} (h : IsCornerUnitary V G) (y : ℝ) :
    mtTrans G y * V = V * mtTrans G y := by
  unfold mtTrans
  split_ifs with hpos
  · rw [Matrix.smul_mul, Matrix.mul_smul, h.commutes]
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

@[simp]
theorem mtTrans_zero (G : Matrix n n ℂ) : mtTrans G 0 = 0 := by
  rw [mtTrans, if_pos le_rfl]
  norm_num

end Transition

/-! ## 4. Circle charts -/

section Circle

/-- A **circle chart** on a space `Z`: two continuous coordinates with `y² + t² = 1`.
Everything below is stated for an arbitrary circle chart, so a downstream lane may present
`S¹` in whichever model its cohomology layer prefers; `sphereOne` is the model this lane
records. -/
structure IsCircleChart {Z : Type*} [TopologicalSpace Z] (y t : Z → ℝ) : Prop where
  /-- The horizontal coordinate is continuous. -/
  continuous_horiz : Continuous y
  /-- The height is continuous. -/
  continuous_height : Continuous t
  /-- The two coordinates lie on the unit circle. -/
  circle : ∀ z, (y z) ^ 2 + (t z) ^ 2 = 1

/-- The circle of this lane: the unit sphere of the Euclidean plane, matching the repo's
`sphereFour`/`sphereFive` convention. -/
abbrev sphereOne : Set (EuclideanSpace ℝ (Fin 2)) := Metric.sphere 0 1

/-- The horizontal coordinate of the circle. -/
def circHoriz (z : ↥sphereOne) : ℝ := (z : EuclideanSpace ℝ (Fin 2)) 0

/-- The height coordinate of the circle. -/
def circHeight (z : ↥sphereOne) : ℝ := (z : EuclideanSpace ℝ (Fin 2)) 1

theorem circ_sq_add_sq (z : ↥sphereOne) : circHoriz z ^ 2 + circHeight z ^ 2 = 1 := by
  have hz : ‖(z : EuclideanSpace ℝ (Fin 2))‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  have hsq : ‖(z : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = ∑ i, (z : EuclideanSpace ℝ (Fin 2)) i ^ 2 :=
    EuclideanSpace.real_norm_sq_eq _
  rw [hz, one_pow, Fin.sum_univ_two] at hsq
  exact hsq.symm

/-- The circle chart of `sphereOne`. -/
theorem isCircleChart_sphereOne : IsCircleChart circHoriz circHeight where
  continuous_horiz := (PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val
  continuous_height := (PiLp.continuous_apply 2 _ 1).comp continuous_subtype_val
  circle := circ_sq_add_sq

private theorem norm_toLp_two (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ‖(WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
  have hsq : ‖(WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simpa using hab
  nlinarith [norm_nonneg (WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2))]

/-- The **north pole**, the slice at which the mapping torus restricts to `V ⊕ 0`. -/
def northPole : ↥sphereOne :=
  ⟨WithLp.toLp 2 ![0, 1], mem_sphere_zero_iff_norm.mpr (norm_toLp_two 0 1 (by norm_num))⟩

@[simp]
theorem circHoriz_northPole : circHoriz northPole = 0 := rfl

@[simp]
theorem circHeight_northPole : circHeight northPole = 1 := rfl

/-- The **south pole**, where the manuscript's section has its single zero. -/
def southPole : ↥sphereOne :=
  ⟨WithLp.toLp 2 ![0, -1], mem_sphere_zero_iff_norm.mpr (norm_toLp_two 0 (-1) (by norm_num))⟩

@[simp]
theorem circHoriz_southPole : circHoriz southPole = 0 := rfl

@[simp]
theorem circHeight_southPole : circHeight southPole = -1 := rfl

/-- On a circle chart, height `-1` forces the horizontal coordinate to vanish. -/
theorem horiz_eq_zero_of_height_eq_neg_one {Z : Type*} [TopologicalSpace Z] {y t : Z → ℝ}
    (h : IsCircleChart y t) {z : Z} (hz : t z = -1) : y z = 0 := by
  have hc := h.circle z
  rw [hz] at hc
  nlinarith [sq_nonneg (y z)]

/-- On a circle chart, height `1` forces the horizontal coordinate to vanish. -/
theorem horiz_eq_zero_of_height_eq_one {Z : Type*} [TopologicalSpace Z] {y t : Z → ℝ}
    (h : IsCircleChart y t) {z : Z} (hz : t z = 1) : y z = 0 := by
  have hc := h.circle z
  rw [hz] at hc
  nlinarith [sq_nonneg (y z)]

end Circle

/-! ## 5. The mapping torus -/

section MappingTorus

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {M : Type*} [TopologicalSpace M] {Z : Type*} [TopologicalSpace Z]

/-- The diagonal doubling of a projection. -/
def double (V : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.fromBlocks V 0 0 V

theorem double_conjTranspose {V : Matrix n n ℂ} (hV : IsStarProjection V) :
    (double V)ᴴ = double V := by
  rw [double, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    proj_conjTranspose hV]

theorem double_mul_self {V : Matrix n n ℂ} (hV : IsStarProjection V) :
    double V * double V = double V := by
  have hVV : V * V = V := hV.isIdempotentElem.eq
  rw [double, Matrix.fromBlocks_multiply]
  simp [hVV]

/-- Continuity of a `2 × 2` block assembly. -/
theorem continuous_fromBlocks' {X : Type*} [TopologicalSpace X]
    {A B C D : X → Matrix n n ℂ} (hA : Continuous A) (hB : Continuous B) (hC : Continuous C)
    (hD : Continuous D) :
    Continuous fun x => Matrix.fromBlocks (A x) (B x) (C x) (D x) := by
  refine continuous_matrix fun i j => ?_
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa using hA.matrix_elem i j
    | inr j => simpa using hB.matrix_elem i j
  | inr i =>
    cases j with
    | inl j => simpa using hC.matrix_elem i j
    | inr j => simpa using hD.matrix_elem i j

/-- The clutched projection commutes with the doubled projection whenever the transition
matrix does. -/
theorem mtProj_mul_double_comm {t : ℝ} {f V : Matrix n n ℂ} (hV : IsStarProjection V)
    (hc : f * V = V * f) : mtProj t f * double V = double V * mtProj t f := by
  have hc' : fᴴ * V = V * fᴴ := by
    have hd := congrArg Matrix.conjTranspose hc
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, proj_conjTranspose hV] at hd
    exact hd.symm
  rw [mtProj_eq, double, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · simp [Matrix.smul_mul, Matrix.mul_smul]
  · simp [Matrix.smul_mul, Matrix.mul_smul, hc']
  · simp [Matrix.smul_mul, Matrix.mul_smul, hc]
  · simp [Matrix.smul_mul, Matrix.mul_smul]

/-- **The mapping torus bundle `W_g`.**  Over the circle chart `(y, t)` of `Z` and the
base `M` it is the clutched family cut down to the range of `V`. -/
def mappingTorus (V G : M → Matrix n n ℂ) (y t : Z → ℝ) (p : Z × M) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  mtProj (t p.1) (mtTrans (G p.2) (y p.1)) * double (V p.2)

variable {V G : M → Matrix n n ℂ} {y t : Z → ℝ}

/-- **`W_g` is a projection-valued map.** -/
theorem mappingTorus_isStarProjection (h : ∀ m, IsCornerUnitary (V m) (G m))
    (hch : IsCircleChart y t) (p : Z × M) : IsStarProjection (mappingTorus V G y t p) := by
  have hyt := hch.circle p.1
  have hP := mtProj_isStarProjection (mtTrans_star_mul_self (h p.2) hyt)
    (mtTrans_mul_star_self (h p.2) hyt)
  have hQ : IsStarProjection (double (V p.2)) :=
    ⟨double_mul_self (h p.2).proj, by
      have : star (double (V p.2)) = double (V p.2) := by
        rw [Matrix.star_eq_conjTranspose, double_conjTranspose (h p.2).proj]
      exact this⟩
  have hcomm : mtProj (t p.1) (mtTrans (G p.2) (y p.1)) * double (V p.2)
      = double (V p.2) * mtProj (t p.1) (mtTrans (G p.2) (y p.1)) :=
    mtProj_mul_double_comm (h p.2).proj (mtTrans_commutes (h p.2) (y p.1))
  set P := mtProj (t p.1) (mtTrans (G p.2) (y p.1)) with hPdef
  set Q := double (V p.2) with hQdef
  constructor
  · show mappingTorus V G y t p * mappingTorus V G y t p = mappingTorus V G y t p
    rw [mappingTorus, ← hPdef, ← hQdef]
    have key : P * Q * (P * Q) = P * (Q * P) * Q := by noncomm_ring
    rw [key, ← hcomm]
    have key2 : P * (P * Q) * Q = P * P * (Q * Q) := by noncomm_ring
    rw [key2, hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq]
  · show star (mappingTorus V G y t p) = mappingTorus V G y t p
    rw [mappingTorus, ← hPdef, ← hQdef, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_mul]
    rw [show Qᴴ = Q from double_conjTranspose (h p.2).proj,
      show Pᴴ = P from mtProj_conjTranspose _ _, ← hcomm]

/-- **`W_g` is continuous.** -/
theorem mappingTorus_continuous (hV : Continuous V) (hG : Continuous G)
    (hch : IsCircleChart y t) : Continuous (mappingTorus V G y t) := by
  have hy : Continuous fun p : Z × M => y p.1 := hch.continuous_horiz.comp continuous_fst
  have ht : Continuous fun p : Z × M => t p.1 := hch.continuous_height.comp continuous_fst
  have hGm : Continuous fun p : Z × M => G p.2 := hG.comp continuous_snd
  have hVm : Continuous fun p : Z × M => V p.2 := hV.comp continuous_snd
  have hf : Continuous fun p : Z × M => mtTrans (G p.2) (y p.1) := by
    simp only [mtTrans]
    refine Continuous.if_le ((Complex.continuous_ofReal.comp hy).smul hGm)
      ((Complex.continuous_ofReal.comp hy.neg).smul continuous_const) continuous_const hy
      (fun p hp => ?_)
    rw [← hp]
    simp
  have hProj : Continuous fun p : Z × M => mtProj (t p.1) (mtTrans (G p.2) (y p.1)) := by
    simp only [mtProj, mtSym]
    refine continuous_const.smul (continuous_const.add ?_)
    exact continuous_fromBlocks' ((Complex.continuous_ofReal.comp ht).smul continuous_const)
      hf.matrix_conjTranspose hf
      (((Complex.continuous_ofReal.comp ht).neg).smul continuous_const)
  refine hProj.matrix_mul ?_
  simp only [double]
  exact continuous_fromBlocks' hVm continuous_const continuous_const hVm

/-- **The north-pole slice.**  At a circle point with `y = 0` and `t = 1` the mapping torus
is `V ⊕ 0` on the nose, so `W_g|_{slice} = V` with no equivalence to transport. -/
theorem mappingTorus_north {z : Z} (hy : y z = 0) (ht : t z = 1) (m : M) :
    mappingTorus V G y t (z, m) = Matrix.fromBlocks (V m) 0 0 0 := by
  rw [mappingTorus]
  simp only [hy, ht, mtTrans_zero]
  rw [mtProj_eq, double, Matrix.fromBlocks_multiply]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_zero, add_zero]
    norm_num
  · simp
  · simp
  · rw [Matrix.mul_zero, Matrix.smul_mul, Matrix.one_mul, zero_add]
    norm_num

/-- **The south-pole slice** is `0 ⊕ V`. -/
theorem mappingTorus_south {z : Z} (hy : y z = 0) (ht : t z = -1) (m : M) :
    mappingTorus V G y t (z, m) = Matrix.fromBlocks 0 0 0 (V m) := by
  rw [mappingTorus]
  simp only [hy, ht, mtTrans_zero]
  rw [mtProj_eq, double, Matrix.fromBlocks_multiply]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_zero, add_zero]
    norm_num
  · simp
  · simp
  · rw [Matrix.mul_zero, Matrix.smul_mul, Matrix.one_mul, zero_add]
    norm_num

/-- The trace of a `2 × 2` block matrix is the sum of the diagonal blocks' traces. -/
theorem trace_fromBlocks' (A B C D : Matrix n n ℂ) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

/-- **The rank of `W_g` is the rank of `V`.**  For projections over `ℂ` the rank is the
trace, and the trace of the mapping torus at every point of `S¹ × M` equals the trace of
`V` at the corresponding point of `M`. -/
theorem trace_mappingTorus (p : Z × M) :
    Matrix.trace (mappingTorus V G y t p) = Matrix.trace (V p.2) := by
  rw [mappingTorus, mtProj_eq, double, Matrix.fromBlocks_multiply, trace_fromBlocks']
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.smul_mul,
    Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
  rw [← add_mul, show ((((1 + t p.1) / 2 : ℝ)) : ℂ) + ((((1 - t p.1) / 2 : ℝ)) : ℂ) = 1 by
    push_cast; ring, one_mul]

end MappingTorus

end GroupApproximation.CharClass
