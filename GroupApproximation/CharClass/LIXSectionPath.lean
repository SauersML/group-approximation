import GroupApproximation.CharClass.MappingTorusSection

/-!
# The manuscript's path (2.10) as a section of the mapping torus

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

The counterexample manuscript
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`,
proof of Lemma 2) uses the section

```text
S (x, y, τ) = ((1 - τ) e₃ + τ x, χ τ · σ y)                              (2.10)
```

of `V = 1³ ⊕ H`, running from the unit section `e` at `τ = 0` to the unit section `s` at
`τ = 1`.  In the clutching model of `GroupApproximation/CharClass/MappingTorusProjection.lean`
the circle's southern arc is parametrised by its horizontal coordinate, so the path is
plugged in with

```text
τ (z) = (1 + y z) / 2 ,
```

an affine function of the circle coordinate — no `arccos`, no `arctan`, and no chart
gluing.  It runs from `τ = 0` at the equator point `y = -1` to `τ = 1` at the equator
point `y = 1`, and takes the value `1/2` exactly at the south pole.

The northern field is the **constant** `e`.  The seam condition of `IsMTSectionData` then
reads `G *ᵥ e = s` — the manuscript's own `g e = s` — and this file proves that it is
exactly what makes the pair descend.

## Main results

* `unitVectors_seam_eq_zero_iff` — for unit vectors `a, b` of `ℂ^ι` and `τ ∈ [0,1]`, the
  straight path `(1-τ) a + τ b` passes through the origin iff `τ = 1/2` and `b = -a`.
* `manuscriptPath`, `southParam` — the path and the circle parameter.
* `isMTSectionData_manuscript` — the pair `(e, path)` is section data, **given** `G e = s`.
* `manuscriptPath_eq_zero_iff_split` — the zero locus splits along a block decomposition.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix

set_option linter.unusedSectionVars false

/-! ## 1. The straight path between two unit vectors -/

/-- **The manuscript's `ℂ³`-component vanishes only at the midpoint of an antipodal
pair.**  Stated for the Hermitian unit sphere `∑ ‖a i‖² = 1` of `ℂ^ι`, which is the form
the repo's `unitVectors` takes, so no `EuclideanSpace` type synonym is involved. -/
theorem unitVectors_seam_eq_zero_iff {ι : Type*} [Fintype ι] {a b : ι → ℂ}
    (ha : ∑ i, ‖a i‖ ^ 2 = 1) (hb : ∑ i, ‖b i‖ ^ 2 = 1) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    (∀ i, ((1 - τ : ℝ) : ℂ) * a i + ((τ : ℝ) : ℂ) * b i = 0)
      ↔ (τ = 1 / 2 ∧ ∀ i, b i = -a i) := by
  constructor
  · intro h
    have hpt : ∀ i, ((1 - τ : ℝ) : ℂ) * a i = -(((τ : ℝ) : ℂ) * b i) := fun i =>
      eq_neg_of_add_eq_zero_left (h i)
    have hnorm : ∀ i, (1 - τ) ^ 2 * ‖a i‖ ^ 2 = τ ^ 2 * ‖b i‖ ^ 2 := by
      intro i
      have h2 := congrArg (fun z : ℂ => ‖z‖ ^ 2) (hpt i)
      simp only [norm_mul, norm_neg, Complex.norm_real, mul_pow, sq_abs] at h2
      exact h2
    have hsum : (1 - τ) ^ 2 = τ ^ 2 := by
      have := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hnorm i)
      rw [← Finset.mul_sum, ← Finset.mul_sum, ha, hb, mul_one, mul_one] at this
      exact this
    have hτ : τ = 1 / 2 := by nlinarith
    refine ⟨hτ, fun i => ?_⟩
    have hi := hpt i
    rw [hτ] at hi
    have h2 : ((1 - 1 / 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [h2] at hi
    have hne : (((1 / 2 : ℝ)) : ℂ) ≠ 0 := by norm_num
    field_simp at hi
    linear_combination hi
  · rintro ⟨hτ, hab⟩ i
    rw [hτ, hab i]
    push_cast
    ring

/-! ## 2. The path and the circle parameter -/

section Path

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {M : Type*} [TopologicalSpace M] {Z : Type*} [TopologicalSpace Z]

/-- **The manuscript's path (2.10).**  `e`, `s` are unit sections of `V` and `σ` is the
transverse section of the `H`-block; `χ` vanishes at both endpoints and equals `1` at
`1/2`. -/
def manuscriptPath (e s σ : M → n → ℂ) (χ : ℝ → ℝ) (τ : ℝ) (m : M) : n → ℂ :=
  fun i => ((1 - τ : ℝ) : ℂ) * e m i + ((τ : ℝ) : ℂ) * s m i + ((χ τ : ℝ) : ℂ) * σ m i

@[simp]
theorem manuscriptPath_apply (e s σ : M → n → ℂ) (χ : ℝ → ℝ) (τ : ℝ) (m : M) (i : n) :
    manuscriptPath e s σ χ τ m i =
      ((1 - τ : ℝ) : ℂ) * e m i + ((τ : ℝ) : ℂ) * s m i + ((χ τ : ℝ) : ℂ) * σ m i := rfl

/-- The endpoint `τ = 0` of the path is `e`. -/
theorem manuscriptPath_zero {e s σ : M → n → ℂ} {χ : ℝ → ℝ} (hχ : χ 0 = 0) (m : M) :
    manuscriptPath e s σ χ 0 m = e m := by
  funext i
  rw [manuscriptPath_apply, hχ]
  push_cast
  ring

/-- The endpoint `τ = 1` of the path is `s`. -/
theorem manuscriptPath_one {e s σ : M → n → ℂ} {χ : ℝ → ℝ} (hχ : χ 1 = 0) (m : M) :
    manuscriptPath e s σ χ 1 m = s m := by
  funext i
  rw [manuscriptPath_apply, hχ]
  push_cast
  ring

/-- The path takes values in the range of `V` whenever its three fields do. -/
theorem manuscriptPath_mem {V : M → Matrix n n ℂ} {e s σ : M → n → ℂ} {χ : ℝ → ℝ}
    (he : ∀ m, V m *ᵥ e m = e m) (hs : ∀ m, V m *ᵥ s m = s m)
    (hσ : ∀ m, V m *ᵥ σ m = σ m) (τ : ℝ) (m : M) :
    V m *ᵥ manuscriptPath e s σ χ τ m = manuscriptPath e s σ χ τ m := by
  have hsplit : manuscriptPath e s σ χ τ m
      = ((1 - τ : ℝ) : ℂ) • e m + ((τ : ℝ) : ℂ) • s m + ((χ τ : ℝ) : ℂ) • σ m := by
    funext i
    simp [manuscriptPath]
  rw [hsplit, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_smul, he, hs, hσ]

theorem continuous_manuscriptPath {e s σ : M → n → ℂ} {χ : ℝ → ℝ} (he : Continuous e)
    (hs : Continuous s) (hσ : Continuous σ) (hχ : Continuous χ) {τ : Z × M → ℝ}
    (hτ : Continuous τ) :
    Continuous fun p : Z × M => manuscriptPath e s σ χ (τ p) p.2 := by
  have hem : Continuous fun p : Z × M => e p.2 := he.comp continuous_snd
  have hsm : Continuous fun p : Z × M => s p.2 := hs.comp continuous_snd
  have hσm : Continuous fun p : Z × M => σ p.2 := hσ.comp continuous_snd
  refine continuous_pi fun i => ?_
  have hei : Continuous fun p : Z × M => e p.2 i := (continuous_apply i).comp hem
  have hsi : Continuous fun p : Z × M => s p.2 i := (continuous_apply i).comp hsm
  have hσi : Continuous fun p : Z × M => σ p.2 i := (continuous_apply i).comp hσm
  exact ((Complex.continuous_ofReal.comp (continuous_const.sub hτ)).mul hei).add
    (((Complex.continuous_ofReal.comp hτ).mul hsi).add
      ((Complex.continuous_ofReal.comp (hχ.comp hτ)).mul hσi))

/-- **The circle parameter of the southern arc**, an affine function of the horizontal
coordinate: `0` at the equator point `y = -1`, `1` at `y = 1`, `1/2` at the poles. -/
def southParam (y : Z → ℝ) (z : Z) : ℝ := (1 + y z) / 2

theorem continuous_southParam {y : Z → ℝ} (hy : Continuous y) : Continuous (southParam y) := by
  simpa [southParam] using (continuous_const.add hy).div_const 2

@[simp]
theorem southParam_of_one {y : Z → ℝ} {z : Z} (h : y z = 1) : southParam y z = 1 := by
  rw [southParam, h]; norm_num

@[simp]
theorem southParam_of_neg_one {y : Z → ℝ} {z : Z} (h : y z = -1) : southParam y z = 0 := by
  rw [southParam, h]; norm_num

theorem southParam_eq_half_iff {y : Z → ℝ} {z : Z} : southParam y z = 1 / 2 ↔ y z = 0 := by
  rw [southParam]
  constructor
  · intro h; linarith
  · intro h; rw [h]; norm_num

theorem southParam_mem_Icc {y t : Z → ℝ} (hch : IsCircleChart y t) (z : Z) :
    0 ≤ southParam y z ∧ southParam y z ≤ 1 := by
  have hc := hch.circle z
  have h1 : y z ^ 2 ≤ 1 := by nlinarith [sq_nonneg (t z)]
  have h2 : -1 ≤ y z := by nlinarith [sq_nonneg (y z + 1)]
  have h3 : y z ≤ 1 := by nlinarith [sq_nonneg (y z - 1)]
  constructor <;> · rw [southParam]; linarith

/-- On a circle chart the equator `{t = 0}` is the two-point set `{y = ±1}`. -/
theorem horiz_eq_one_or_neg_one {y t : Z → ℝ} (hch : IsCircleChart y t) {z : Z}
    (hz : t z = 0) : y z = 1 ∨ y z = -1 := by
  have hc := hch.circle z
  rw [hz] at hc
  have : (y z - 1) * (y z + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-! ## 3. The manuscript's pair is section data -/

variable {V G : M → Matrix n n ℂ} {y t : Z → ℝ} {e s σ : M → n → ℂ} {χ : ℝ → ℝ}

/-- **The manuscript's section data.**  Northern field the constant `e`, southern field the
path (2.10) reparametrised by the circle's horizontal coordinate.  The seam condition is
exactly the manuscript's `g e = s`. -/
theorem isMTSectionData_manuscript (hch : IsCircleChart y t) (he : Continuous e)
    (hs : Continuous s) (hσ : Continuous σ) (hχ : Continuous χ) (hχ0 : χ 0 = 0)
    (hχ1 : χ 1 = 0) (heV : ∀ m, V m *ᵥ e m = e m) (hsV : ∀ m, V m *ᵥ s m = s m)
    (hσV : ∀ m, V m *ᵥ σ m = σ m) (hGe : ∀ m, G m *ᵥ e m = s m) :
    IsMTSectionData V G y t (fun p : Z × M => e p.2)
      (fun p : Z × M => manuscriptPath e s σ χ (southParam y p.1) p.2) where
  continuous_north := he.comp continuous_snd
  continuous_south :=
    continuous_manuscriptPath he hs hσ hχ
      ((continuous_southParam hch.continuous_horiz).comp continuous_fst)
  north_mem := fun p => heV p.2
  south_mem := fun p => manuscriptPath_mem heV hsV hσV _ p.2
  seam := fun p hp => by
    rcases horiz_eq_one_or_neg_one hch hp with hy | hy
    · rw [southParam_of_one hy, manuscriptPath_one hχ1, mtTrans, if_pos (by rw [hy]; norm_num),
        hy]
      rw [show ((1 : ℝ) : ℂ) • G p.2 = G p.2 by norm_num, hGe p.2]
    · rw [southParam_of_neg_one hy, manuscriptPath_zero hχ0, mtTrans,
        if_neg (by rw [hy]; norm_num), hy]
      rw [show ((-(-1 : ℝ) : ℝ) : ℂ) • (1 : Matrix n n ℂ) = 1 by norm_num,
        Matrix.one_mulVec]

/-! ## 4. Splitting the zero locus along the two blocks -/

section Split

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **The zero locus of (2.10) splits.**  With `e = (a, 0)`, `s = (b, 0)` supported on the
first block and `σ = (0, c)` on the second, the path vanishes iff the straight path
`(1-τ) a + τ b` and the scaled `χ τ · c` both vanish. -/
theorem manuscriptPath_eq_zero_iff_split {N : Type*} {a b : N → ι → ℂ} {c : N → κ → ℂ}
    (χ : ℝ → ℝ) (τ : ℝ) (m : N) :
    manuscriptPath (fun m => Sum.elim (a m) 0) (fun m => Sum.elim (b m) 0)
        (fun m => Sum.elim 0 (c m)) χ τ m = 0
      ↔ ((∀ i, ((1 - τ : ℝ) : ℂ) * a m i + ((τ : ℝ) : ℂ) * b m i = 0) ∧
          ∀ k, ((χ τ : ℝ) : ℂ) * c m k = 0) := by
  constructor
  · intro h
    constructor
    · intro i
      have hi := congrFun h (Sum.inl i)
      simpa using hi
    · intro k
      have hk := congrFun h (Sum.inr k)
      simpa using hk
  · rintro ⟨h1, h2⟩
    funext j
    cases j with
    | inl i => simpa using h1 i
    | inr k => simpa using h2 k

end Split

end Path

end GroupApproximation.CharClass
