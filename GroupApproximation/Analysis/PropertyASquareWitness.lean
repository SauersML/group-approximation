import GroupApproximation.Analysis.ExactnessPermanence
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt

/-!
# From `ℓ²` columns to property A: the square trick

Guentner--Kaminker's Theorem 3.2 produces, at the end, a *finite width positive
definite kernel* `û(s,t) = ⟨W δ_t, W δ_s⟩` uniformly close to `1` on strips,
where `W` is an operator of finite propagation.  What that gives concretely is
a family of vectors

```
    ζ_s = W δ_s ∈ ℓ²(Γ) ,   supported in  s · F   for one finite `F`,
```

with `‖ζ_s‖² ≈ 1` and `‖ζ_s - ζ_t‖² = û(s,s) + û(t,t) - 2û(s,t)` small on
strips.  Yu's property A, in the form `ExactnessPermanence.PropertyAWitness`
uses, asks instead for *probability measures* --- an `ℓ¹` condition.

This module is the bridge, and it is unconditional: **squaring the entries**
turns an `ℓ²` system into an `ℓ¹` system, at the cost of a fixed constant.  The
mechanism is one line of Cauchy--Schwarz,

```
    Σ |a² - b²|  =  Σ |a - b|·|a + b|  ≤  ‖a - b‖₂ · ‖a + b‖₂ ,
```

so an `ℓ²` displacement `ε` between vectors of norm about `1` becomes an `ℓ¹`
displacement of order `ε` between the squared measures.  This is the standard
half of Higson--Roe's equivalence, and it is the half that needs no analysis.

## Why the normalisation is approximate

The vectors coming out of an operator approximation have `‖ζ_s‖² ≈ 1`, not
`= 1`.  Rather than renormalise upstream --- where the estimate would have to
be carried through a square root --- `SquareWitness` asks only for
`‖ζ_s‖² ∈ [1/2, 2]` and the division is done here, once.  The price is the
explicit constant `12`, which is of no consequence: property A quantifies over
all tolerances, so any fixed constant is absorbed by rescaling `ε`.

## Statements

* `sq_sum_abs_sq_sub_le` --- the Cauchy--Schwarz step;
* `SquareWitness` --- an `ℓ²` system with translate-controlled supports,
  approximate normalisation, and small displacement on the scale `R`;
* `SquareWitness.toPropertyAWitness` --- squaring, normalising, and the `ℓ¹`
  estimate: a `SquareWitness` at tolerance `ε` is a `PropertyAWitness` at
  tolerance `12ε`;
* `hasPropertyA_of_squareWitness` --- consequently a group with `ℓ²` systems at
  every scale and tolerance has property A.
-/

namespace GroupApproximation
namespace PropertyASquareWitness

open ExactnessPermanence

universe u

variable {G : Type u} [Group G]

/-! ## The Cauchy--Schwarz step -/

/-- `Σ|a² - b²| ≤ ‖a-b‖₂ ‖a+b‖₂`, in squared form so that no square root is
needed.  This is the only inequality in the passage from `ℓ²` to `ℓ¹`. -/
theorem sq_sum_abs_sq_sub_le {ι : Type*} (T : Finset ι) (a b : ι → ℝ) :
    (∑ x ∈ T, |a x ^ 2 - b x ^ 2|) ^ 2
      ≤ (∑ x ∈ T, (a x - b x) ^ 2) * ∑ x ∈ T, (a x + b x) ^ 2 := by
  have hfac : ∀ x ∈ T, |a x ^ 2 - b x ^ 2| = |a x - b x| * |a x + b x| := by
    intro x _
    rw [← abs_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl hfac]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq T (fun x ↦ |a x - b x|) (fun x ↦ |a x + b x|)
  simpa [sq_abs] using hCS

/-! ## Windows -/

/-- **The window lemma.**  A sum of squares of a function supported in the
translate `g · template` may be computed over any finite window containing the
support: both sides are the sum over the support.

This is stated free of the witness structures because both the construction of
an `ℓ²` witness and its use need it. -/
theorem sum_sq_window_eq {template : Finset G} {v : G → ℝ} (g : G) {T : Finset G}
    (hsupp : ∀ x, g⁻¹ * x ∉ template → v x = 0) (hT : ∀ x, v x ≠ 0 → x ∈ T) :
    ∑ x ∈ T, v x ^ 2 = ∑ s ∈ template, v (g * s) ^ 2 := by
  classical
  set Tg : Finset G := template.image (fun s ↦ g * s) with hTgdef
  have hmemTg : ∀ x : G, x ∈ Tg ↔ g⁻¹ * x ∈ template := by
    intro x
    rw [hTgdef, Finset.mem_image]
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa using hs
    · intro hx
      exact ⟨g⁻¹ * x, hx, by simp⟩
  have hzeroT : ∀ x ∈ T ∪ Tg, x ∉ T → v x ^ 2 = 0 := by
    intro x _ hx
    have hv : v x = 0 := by
      by_contra hc
      exact hx (hT x hc)
    simp [hv]
  have hzeroTg : ∀ x ∈ T ∪ Tg, x ∉ Tg → v x ^ 2 = 0 := by
    intro x _ hx
    have hnot : g⁻¹ * x ∉ template := fun hc ↦ hx ((hmemTg x).mpr hc)
    simp [hsupp x hnot]
  have e₁ : ∑ x ∈ T, v x ^ 2 = ∑ x ∈ T ∪ Tg, v x ^ 2 :=
    Finset.sum_subset Finset.subset_union_left hzeroT
  have e₂ : ∑ x ∈ Tg, v x ^ 2 = ∑ x ∈ T ∪ Tg, v x ^ 2 :=
    Finset.sum_subset Finset.subset_union_right hzeroTg
  have e₃ : ∑ x ∈ Tg, v x ^ 2 = ∑ s ∈ template, v (g * s) ^ 2 := by
    rw [hTgdef]
    refine Finset.sum_image ?_
    intro x _ y _ hxy
    exact mul_left_cancel hxy
  rw [e₁, ← e₂, e₃]

/-! ## `ℓ²` witnesses -/

/-- An **`ℓ²` witness** for property A at scale `R` and tolerance `ε`: a family
of vectors `vec g ∈ ℓ²(G)`, supported in the translate `g · template` of one
finite set, of squared norm between `1/2` and `2`, and moving by at most `ε` in
`ℓ²` when the base point moves inside `R`.

The support and closeness clauses are stated exactly as in
`PropertyAWitness`: supports are `g`-relative, and the `ℓ²` estimate is
quantified over every finite window containing both supports, which is what
makes it the honest `ℓ²` norm of the difference. -/
structure SquareWitness (G : Type u) [Group G] (R : Finset G) (ε : ℝ) where
  /-- The finite template; the vector at `g` lives on `g · template`. -/
  template : Finset G
  /-- `vec g x` is the `x`-coordinate of the vector attached to `g`. -/
  vec : G → G → ℝ
  /-- The vector attached to `g` is supported inside `g · template`. -/
  vec_eq_zero : ∀ g x, g⁻¹ * x ∉ template → vec g x = 0
  /-- The vectors are not too small. -/
  mass_lower : ∀ g, 1 / 2 ≤ ∑ s ∈ template, vec g (g * s) ^ 2
  /-- The vectors are not too big. -/
  mass_upper : ∀ g, (∑ s ∈ template, vec g (g * s) ^ 2) ≤ 2
  /-- Base points at distance at most `R` carry vectors at `ℓ²` distance at
  most `ε`. -/
  vec_close : ∀ g h, g⁻¹ * h ∈ R → ∀ T : Finset G,
    (∀ x, vec g x ≠ 0 → x ∈ T) → (∀ x, vec h x ≠ 0 → x ∈ T) →
      ∑ x ∈ T, (vec g x - vec h x) ^ 2 ≤ ε ^ 2

namespace SquareWitness

variable {R : Finset G} {ε : ℝ}

/-- The squared `ℓ²` norm of the vector at `g`. -/
def mass (W : SquareWitness G R ε) (g : G) : ℝ :=
  ∑ s ∈ W.template, W.vec g (g * s) ^ 2

theorem mass_pos (W : SquareWitness G R ε) (g : G) : 0 < W.mass g :=
  lt_of_lt_of_le (by norm_num) (W.mass_lower g)

theorem mass_ne_zero (W : SquareWitness G R ε) (g : G) : W.mass g ≠ 0 :=
  ne_of_gt (W.mass_pos g)

/-- The squared `ℓ²` norm of the vector at `g`, computed over any finite window
containing its support. -/
theorem sum_sq_window (W : SquareWitness G R ε) (g : G) {T : Finset G}
    (hT : ∀ x, W.vec g x ≠ 0 → x ∈ T) :
    ∑ x ∈ T, W.vec g x ^ 2 = W.mass g :=
  sum_sq_window_eq g (W.vec_eq_zero g) hT

/-- **Squaring an `ℓ²` witness gives an `ℓ¹` witness.**  The measure attached to
`g` is the normalised square of the vector attached to `g`; supports and total
mass are immediate, and the `ℓ¹` estimate is Cauchy--Schwarz together with the
two-sided bound on the normalisation. -/
noncomputable def toPropertyAWitness (hε : 0 ≤ ε) (W : SquareWitness G R ε) :
    PropertyAWitness G R (12 * ε) where
  template := W.template
  weight := fun g x ↦ W.vec g x ^ 2 / W.mass g
  weight_nonneg := fun g x ↦ div_nonneg (sq_nonneg _) (W.mass_pos g).le
  weight_eq_zero := fun g x hx ↦ by
    rw [W.vec_eq_zero g x hx]
    simp
  weight_sum := fun g ↦ by
    have hm : ∑ s ∈ W.template, W.vec g (g * s) ^ 2 = W.mass g := rfl
    rw [← Finset.sum_div, hm]
    exact div_self (W.mass_ne_zero g)
  weight_close := by
    intro g h hgh T hTg hTh
    have hA0 : 0 < W.mass g := W.mass_pos g
    have hB0 : 0 < W.mass h := W.mass_pos h
    have hAne : W.mass g ≠ 0 := W.mass_ne_zero g
    have hBne : W.mass h ≠ 0 := W.mass_ne_zero h
    have hAlb : 1 / 2 ≤ W.mass g := W.mass_lower g
    have hAub : W.mass g ≤ 2 := W.mass_upper g
    have hBub : W.mass h ≤ 2 := W.mass_upper h
    -- the support hypotheses, transported through the normalisation
    have hTg' : ∀ x, W.vec g x ≠ 0 → x ∈ T := by
      intro x hx
      refine hTg x ?_
      exact div_ne_zero (pow_ne_zero 2 hx) (W.mass_ne_zero g)
    have hTh' : ∀ x, W.vec h x ≠ 0 → x ∈ T := by
      intro x hx
      refine hTh x ?_
      exact div_ne_zero (pow_ne_zero 2 hx) (W.mass_ne_zero h)
    have hAT : ∑ x ∈ T, W.vec g x ^ 2 = W.mass g := W.sum_sq_window g hTg'
    have hBT : ∑ x ∈ T, W.vec h x ^ 2 = W.mass h := W.sum_sq_window h hTh'
    have hclose := W.vec_close g h hgh T hTg' hTh'
    -- the `ℓ¹` displacement of the *unnormalised* squares
    set S : ℝ := ∑ x ∈ T, |W.vec g x ^ 2 - W.vec h x ^ 2| with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun x _ ↦ abs_nonneg _
    have hplus : ∑ x ∈ T, (W.vec g x + W.vec h x) ^ 2 ≤ 8 := by
      have hptwise : ∀ x ∈ T, (W.vec g x + W.vec h x) ^ 2
          ≤ 2 * W.vec g x ^ 2 + 2 * W.vec h x ^ 2 := by
        intro x _
        nlinarith [sq_nonneg (W.vec g x - W.vec h x)]
      calc ∑ x ∈ T, (W.vec g x + W.vec h x) ^ 2
          ≤ ∑ x ∈ T, (2 * W.vec g x ^ 2 + 2 * W.vec h x ^ 2) := Finset.sum_le_sum hptwise
        _ = 2 * (∑ x ∈ T, W.vec g x ^ 2) + 2 * (∑ x ∈ T, W.vec h x ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ 8 := by rw [hAT, hBT]; linarith
    have hSsq : S ^ 2 ≤ (3 * ε) ^ 2 := by
      have hCS := sq_sum_abs_sq_sub_le T (W.vec g) (W.vec h)
      rw [← hSdef] at hCS
      have hpos : 0 ≤ ∑ x ∈ T, (W.vec g x + W.vec h x) ^ 2 :=
        Finset.sum_nonneg fun x _ ↦ sq_nonneg _
      have hmul : (∑ x ∈ T, (W.vec g x - W.vec h x) ^ 2)
          * (∑ x ∈ T, (W.vec g x + W.vec h x) ^ 2) ≤ 8 * ε ^ 2 := by
        have h1 : (∑ x ∈ T, (W.vec g x - W.vec h x) ^ 2)
            * (∑ x ∈ T, (W.vec g x + W.vec h x) ^ 2)
            ≤ ε ^ 2 * (∑ x ∈ T, (W.vec g x + W.vec h x) ^ 2) :=
          mul_le_mul_of_nonneg_right hclose hpos
        have h2 : ε ^ 2 * (∑ x ∈ T, (W.vec g x + W.vec h x) ^ 2) ≤ ε ^ 2 * 8 :=
          mul_le_mul_of_nonneg_left hplus (sq_nonneg ε)
        linarith
      nlinarith [hCS, hmul, sq_nonneg ε]
    have hSle : S ≤ 3 * ε := by
      have h3 : 0 ≤ 3 * ε := by linarith
      have := Real.sqrt_le_sqrt hSsq
      rwa [Real.sqrt_sq hS0, Real.sqrt_sq h3] at this
    -- the two masses differ by at most `S`
    have hBA : |W.mass h - W.mass g| ≤ S := by
      have hsub : W.mass h - W.mass g
          = ∑ x ∈ T, (W.vec h x ^ 2 - W.vec g x ^ 2) := by
        rw [← hAT, ← hBT, ← Finset.sum_sub_distrib]
      have hstep : |∑ x ∈ T, (W.vec h x ^ 2 - W.vec g x ^ 2)|
          ≤ ∑ x ∈ T, |W.vec h x ^ 2 - W.vec g x ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
      have hcomm : ∑ x ∈ T, |W.vec h x ^ 2 - W.vec g x ^ 2|
          = ∑ x ∈ T, |W.vec g x ^ 2 - W.vec h x ^ 2| :=
        Finset.sum_congr rfl fun x _ ↦ abs_sub_comm _ _
      rw [hcomm] at hstep
      rw [hSdef, hsub]
      exact hstep
    -- the pointwise split of the normalised difference
    have hptwise : ∀ x ∈ T,
        |W.vec g x ^ 2 / W.mass g - W.vec h x ^ 2 / W.mass h|
          ≤ |W.vec g x ^ 2 - W.vec h x ^ 2| / W.mass g
            + W.vec h x ^ 2 * |W.mass h - W.mass g| / (W.mass g * W.mass h) := by
      intro x _
      have hAB0 : 0 < W.mass g * W.mass h := mul_pos hA0 hB0
      have hsplit : W.vec g x ^ 2 / W.mass g - W.vec h x ^ 2 / W.mass h
          = (W.vec g x ^ 2 - W.vec h x ^ 2) / W.mass g
            + W.vec h x ^ 2 * (W.mass h - W.mass g) / (W.mass g * W.mass h) := by
        field_simp
        ring
      rw [hsplit]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_div, abs_div, abs_of_pos hA0, abs_of_pos hAB0, abs_mul,
        abs_of_nonneg (sq_nonneg (W.vec h x))]
    -- sum the pointwise estimate
    have hsum : ∑ x ∈ T, |W.vec g x ^ 2 / W.mass g - W.vec h x ^ 2 / W.mass h|
        ≤ S / W.mass g + |W.mass h - W.mass g| / W.mass g := by
      refine le_trans (Finset.sum_le_sum hptwise) ?_
      have hexpand : ∑ x ∈ T, (|W.vec g x ^ 2 - W.vec h x ^ 2| / W.mass g
            + W.vec h x ^ 2 * |W.mass h - W.mass g| / (W.mass g * W.mass h))
          = S / W.mass g
            + (∑ x ∈ T, W.vec h x ^ 2) * |W.mass h - W.mass g| / (W.mass g * W.mass h) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← hSdef]
        congr 1
        rw [← Finset.sum_div, ← Finset.sum_mul]
      rw [hexpand, hBT]
      have hfix : W.mass h * |W.mass h - W.mass g| / (W.mass g * W.mass h)
          = |W.mass h - W.mass g| / W.mass g := by
        field_simp
      rw [hfix]
    -- and finish numerically
    have hfinal : S / W.mass g + |W.mass h - W.mass g| / W.mass g ≤ 12 * ε := by
      have hinv : 0 ≤ (W.mass g)⁻¹ := (inv_pos.mpr hA0).le
      have h1 : |W.mass h - W.mass g| / W.mass g ≤ S / W.mass g := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hBA hinv
      have hd0 : 0 ≤ S / W.mass g := div_nonneg hS0 hA0.le
      have hprod : 0 ≤ (S / W.mass g) * (2 * W.mass g - 1) :=
        mul_nonneg hd0 (by linarith)
      have hexp : (S / W.mass g) * (2 * W.mass g - 1) = 2 * S - S / W.mass g := by
        field_simp
      rw [hexp] at hprod
      have h3 : 0 ≤ ε := hε
      linarith
    exact le_trans hsum hfinal

end SquareWitness

/-- Relaxing the tolerance of a property A witness. -/
def PropertyAWitness.relax {R : Finset G} {ε ε' : ℝ} (hle : ε ≤ ε')
    (W : PropertyAWitness G R ε) : PropertyAWitness G R ε' :=
  { W with
    weight_close := fun g h hgh T h₁ h₂ ↦
      le_trans (W.weight_close g h hgh T h₁ h₂) hle }

/-- **A group with `ℓ²` witnesses at every scale and tolerance has property A.**
This is the unconditional half of Higson--Roe's equivalence, and it is the step
that turns Guentner--Kaminker's finite width kernels into Yu's measures. -/
theorem hasPropertyA_of_squareWitness
    (h : ∀ (R : Finset G) (ε : ℝ), 0 < ε → Nonempty (SquareWitness G R ε)) :
    HasPropertyA G := by
  intro R ε hε
  obtain ⟨W⟩ := h R (ε / 12) (by linarith)
  refine ⟨PropertyAWitness.relax ?_ (W.toPropertyAWitness (by linarith))⟩
  linarith

end PropertyASquareWitness
end GroupApproximation
