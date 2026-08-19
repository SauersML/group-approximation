import GroupApproximation.Analysis.CoarseCompression
import GroupApproximation.Analysis.PropertyASquareWitness

/-!
# Guentner--Kaminker: compression above `1/2` gives property A

`E. Guentner and J. Kaminker, Exactness and uniform embeddability of discrete
groups, J. London Math. Soc. (2) 70 (2004), 703--718` (arXiv `math/0309166`),
Theorem 3.2:

> Let `Γ` be a finitely generated discrete group.  If the Hilbert space
> compression of `Γ` is greater than `1/2` then `Γ` is exact.

Their proof factors through a *group-side* statement and a *crossover*, and the
attribution "Ozawa--Guentner--Kaminker" is exactly that split:

| step | content | reference |
|---|---|---|
| geometric | `R(Γ) > 1/2` ⟹ Gaussian rows are uniformly summable | GK Lemma 3.5, estimate (14) |
| operator | `Op(u_κ)` is a positive element of `C*_u(Γ)`, so `Op(u_κ)^{1/2}` is a norm limit of finite propagation operators | GK Theorem 3.2, closing paragraph |
| crossover | finite width positive definite kernels tending to `1` on strips ⟺ `Γ` exact | Ozawa, *Amenable actions and exactness for discrete groups*, C. R. Acad. Sci. Paris 330 (2000); GK Proposition 3.3 |

This module formalises the group side and states, as one named hypothesis, the
operator step.  The crossover to exactness of `C⋆_red(Γ)` is Ozawa's theorem and
is **not** formalised anywhere in this repository --- it is the standing gap
`E.4` / `SO.16` recorded in `Analysis/ExactnessPermanence.lean` and
`Analysis/CStarExactness.lean`, and nothing here narrows it.  What is reached
instead is `ExactnessPermanence.HasPropertyA`, Yu's property A, which is the
group-side content of GK Proposition 3.3.

## What is proved outright

* `CoarseCompression.exists_tail_bound` and `exists_schur_bound` --- the whole
  of estimate (14): this is where `> 1/2` is consumed, and it is unconditional.
  `gaussianKernel_lemma35_inputs` collects the four properties of the Gaussian
  kernel that Lemma 3.5 begins from.
* `PropertyASquareWitness.hasPropertyA_of_squareWitness` --- the passage from
  finite width `ℓ²` columns to Yu's measures, unconditional.
* `hasPropertyA_of_gaussianRoeApproximation` --- **the assembly**: a
  large-scale Lipschitz map whose Gaussian kernels are approximable by finite
  width squares gives property A.  Unconditional given its hypotheses.
* `hasPropertyA_of_compressionExceeds_half` --- Theorem 3.2's group side, with
  the operator step as a hypothesis.

## What is carried as a hypothesis, and why

Two statements, both named in `hasPropertyA_of_compressionExceeds_half` rather
than assumed silently.

`IsPositiveDefiniteKernel (gaussianKernel f κ)` is **Schoenberg's theorem**:
`‖f s - f t‖²` is a kernel of negative type, so its Gaussian is of positive
type.  Mathlib has neither notion at the pinned revision.

`IsRoeSquareApproximable u` says of a kernel `u` exactly what Guentner--Kaminker
extract in the closing paragraph of their Theorem 3.2: for every `δ` there is a
finite propagation `W`, with matrix coefficients `w`, such that the kernel
`⟨W δ_t, W δ_s⟩` is within `δ` of `u` everywhere.  Their route to it is

1. the Schur test (their Proposition 3.4 (ii)), with the uniform row bound of
   estimate (14), makes `Op(u_κ)` a bounded positive operator, and the vanishing
   tails put it in the **uniform Roe algebra** `C*_u(Γ)`;
2. `C*_u(Γ)` is a C⋆-algebra, so it contains the **positive square root**
   `V_κ = Op(u_κ)^{1/2}`, which is therefore a norm limit of finite propagation
   operators `W`;
3. `|u_κ(s,t) - ⟨W δ_t, W δ_s⟩| ≤ ‖V_κ - W‖(2‖V_κ‖ + ‖V_κ - W‖)`.

These need the Schur test on `ℓ²(Γ)` and the continuous functional calculus
*inside* a closed ⋆-subalgebra.  `Analysis/UniformRoeAlgebra.lean` supplies the
algebra itself (finite propagation operators, the ⋆-subalgebra, its closure) and
its own header records that "everything analytic" for Ozawa's route remains ---
including "Schur multipliers of positive-type kernels".  The hypothesis `hroe`
is stated with precisely the four clauses that
`gaussianKernel_lemma35_inputs` *proves*, so no geometric content is smuggled
into it: what is assumed is the passage through `C*_u(Γ)`, and nothing else.

Note that the *geometric* hypothesis does not appear in the assembly theorem
`hasPropertyA_of_gaussianRoeApproximation` at all, and neither does generation
of the alphabet.  That is faithful to the source: compression above `1/2` is
used only to produce estimate (14), which is an input to step 1; once
`IsRoeSquareApproximable` is granted, all that is still needed is the
large-scale Lipschitz clause, for the convergence condition (8).
-/

namespace GroupApproximation
namespace GuentnerKaminker

open ExactnessPermanence CoarseCompression PropertyASquareWitness

universe u v

variable {G : Type u} [Group G] {E : Type v} [NormedAddCommGroup E]

/-! ## Positive type -/

/-- A kernel is **of positive type** if all its finite quadratic forms are
nonnegative.  For `u_κ(s,t) = exp(-κ‖f s - f t‖²)` this is Schoenberg's theorem
applied to the negative type kernel `‖f s - f t‖²`; Mathlib has neither, so it
appears below as a named hypothesis rather than as a proved fact. -/
def IsPositiveDefiniteKernel (u : G → G → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℝ),
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, c i * c j * u (x i) (x j)

/-! ## The operator step, named -/

/-- **`u` is approximable by finite width squares.**  For every tolerance there
is a family `w` of finite propagation --- `w s x` vanishes unless `s⁻¹x` lies in
one fixed finite set --- whose Gram kernel `Σₓ w s x · w t x` is within `δ` of
`u` at every pair.

This is what Guentner--Kaminker's Theorem 3.2 produces from
`W ∈ C*_u(Γ)` approximating `Op(u)^{1/2}`, with `w s x = ⟨W δ_s, δ_x⟩`; the
Gram kernel is then `⟨W δ_t, W δ_s⟩`, which is automatically positive definite
and of finite width.  See the module header for what proving it would require.

The inner sum is quantified over every finite window containing both supports,
which is the finite-sum spelling of `⟨W δ_t, W δ_s⟩`: outside such a window
every term vanishes. -/
def IsRoeSquareApproximable (u : G → G → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (F : Finset G) (w : G → G → ℝ),
    (∀ s x, s⁻¹ * x ∉ F → w s x = 0) ∧
    ∀ (s t : G) (T : Finset G), (∀ x, w s x ≠ 0 → x ∈ T) → (∀ x, w t x ≠ 0 → x ∈ T) →
      |u s t - ∑ x ∈ T, w s x * w t x| ≤ δ

/-- The operator step for the whole Gaussian family `u_κ`, `κ > 0`, of a fixed
map. -/
def GaussianRoeApproximation (f : G → E) : Prop :=
  ∀ κ : ℝ, 0 < κ → IsRoeSquareApproximable (gaussianKernel f κ)

/-! ## What the compression hypothesis proves -/

/-- **The inputs of Guentner--Kaminker's Lemma 3.5, all proved.**  For a
large-scale Lipschitz map with compression exponent above `1/2`, the Gaussian
kernel at any positive `κ` is normalised on the diagonal, symmetric, has rows of
uniformly bounded mass, and has uniformly vanishing tails.

The third and fourth clauses are estimate (14); they are the only place in the
whole argument where `> 1/2` is used, and they are unconditional. -/
theorem gaussianKernel_lemma35_inputs {T : Finset G}
    (hT : WordMetric.IsSymmetricGeneratingSet (↑T : Set G))
    {f : G → E} {β : ℝ} (hβ : 1 / 2 < β)
    (hcomp : HasCompressionExponent (↑T : Set G) f β) {κ : ℝ} (hκ : 0 < κ) :
    (∀ s : G, gaussianKernel f κ s s = 1) ∧
    (∀ s t : G, gaussianKernel f κ s t = gaussianKernel f κ t s) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (s : G) (F : Finset G),
      ∑ t ∈ F, gaussianKernel f κ s t ≤ C) ∧
    (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ (s : G) (F : Finset G),
      (∀ t ∈ F, N < WordMetric.wordDist (↑T : Set G) s t) →
        ∑ t ∈ F, gaussianKernel f κ s t ≤ δ) := by
  refine ⟨gaussianKernel_self f κ, gaussianKernel_comm f κ,
    exists_schur_bound hT hβ hcomp hκ, ?_⟩
  intro δ hδ
  exact exists_tail_bound hT hβ hcomp hκ hδ

/-! ## The assembly -/

/-- **Guentner--Kaminker, assembled.**  A large-scale Lipschitz map whose
Gaussian kernels are approximable by finite width squares gives Yu's property A.

The proof is the last two paragraphs of their Theorem 3.2, read in the `ℓ²`
picture.  Fix a scale `R` and a tolerance `ε`.  Every element of `R` has word
length at most `Rad`, so the convergence condition
`1 - u_κ(g,h) ≤ κ(C·Rad + D)²` makes `u_κ` as close to `1` on the scale `R` as
we please once `κ` is small.  Take the finite width approximant `w` at tolerance
`δ`; its columns `ζ_g = w g (·)` are supported in `g · F`, have

```
    ‖ζ_g‖² = Σₓ w g x · w g x  ∈  [1 - δ, 1 + δ]     (from  u_κ(g,g) = 1),
    ‖ζ_g - ζ_h‖² = ‖ζ_g‖² + ‖ζ_h‖² - 2⟨ζ_g, ζ_h⟩ ≤ 2(1 - u_κ(g,h)) + 4δ ,
```

and the second is small on the scale `R` by the convergence condition.  So the
columns are an `ℓ²` witness, and `PropertyASquareWitness` squares them into
Yu's measures. -/
theorem hasPropertyA_of_gaussianRoeApproximation {T : Finset G}
    {f : G → E} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ x y : G, ‖f x - f y‖ ≤ C * (WordMetric.wordDist (↑T : Set G) x y : ℝ) + D)
    (hroe : GaussianRoeApproximation f) :
    HasPropertyA G := by
  classical
  refine hasPropertyA_of_squareWitness ?_
  intro R ε hε
  -- every element of the scale has word length at most `Rad`
  set Rad : ℕ := ∑ r ∈ R, WordMetric.wordNorm (↑T : Set G) r
  have hRad : ∀ g h : G, g⁻¹ * h ∈ R → WordMetric.wordDist (↑T : Set G) g h ≤ Rad := by
    intro g h hgh
    have hsingle := Finset.single_le_sum
      (f := fun r ↦ WordMetric.wordNorm (↑T : Set G) r) (fun i _ ↦ Nat.zero_le _) hgh
    show WordMetric.wordNorm (↑T : Set G) (g⁻¹ * h) ≤ Rad
    exact hsingle
  -- choose the Gaussian parameter so that the kernel is `ε²/8`-close to `1` on the scale
  obtain ⟨κ, hκ, hκP⟩ :
      ∃ κ : ℝ, 0 < κ ∧ κ * (C * (Rad : ℝ) + D) ^ 2 ≤ ε ^ 2 / 8 := by
    have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
    have hnum : (0 : ℝ) < ε ^ 2 / 8 := by linarith
    have hden : (0 : ℝ) < (C * (Rad : ℝ) + D) ^ 2 + 1 := by positivity
    have hden' : ((C * (Rad : ℝ) + D) ^ 2 + 1) ≠ 0 := ne_of_gt hden
    refine ⟨(ε ^ 2 / 8) / ((C * (Rad : ℝ) + D) ^ 2 + 1), div_pos hnum hden, ?_⟩
    have hstep : (ε ^ 2 / 8) / ((C * (Rad : ℝ) + D) ^ 2 + 1) * (C * (Rad : ℝ) + D) ^ 2
        ≤ (ε ^ 2 / 8) / ((C * (Rad : ℝ) + D) ^ 2 + 1) * ((C * (Rad : ℝ) + D) ^ 2 + 1) := by
      refine mul_le_mul_of_nonneg_left (by linarith) ?_
      positivity
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  -- choose the approximation tolerance
  obtain ⟨δ, hδ, hδhalf, hδeps⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ δ ≤ ε ^ 2 / 16 :=
    ⟨min (1 / 2) (ε ^ 2 / 16),
      lt_min (by norm_num) (by have := pow_pos hε 2; linarith),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨F, w, hsupp, happ⟩ := hroe κ hκ δ hδ
  -- the translated template is a window for every column
  have hwin : ∀ g : G, ∀ x, w g x ≠ 0 → x ∈ F.image (fun s ↦ g * s) := by
    intro g x hx
    have hmemF : g⁻¹ * x ∈ F := by
      by_contra hc
      exact hx (hsupp g x hc)
    exact Finset.mem_image.mpr ⟨g⁻¹ * x, hmemF, by simp⟩
  -- the columns are almost unit vectors
  have hmassabs : ∀ g : G, |1 - ∑ s ∈ F, w g (g * s) ^ 2| ≤ δ := by
    intro g
    have h := happ g g (F.image (fun s ↦ g * s)) (hwin g) (hwin g)
    rw [gaussianKernel_self] at h
    have hsq : ∑ x ∈ F.image (fun s ↦ g * s), w g x * w g x
        = ∑ s ∈ F, w g (g * s) ^ 2 := by
      have hrw : ∀ x ∈ F.image (fun s ↦ g * s), w g x * w g x = w g x ^ 2 :=
        fun x _ ↦ (pow_two (w g x)).symm
      rw [Finset.sum_congr rfl hrw]
      exact sum_sq_window_eq g (hsupp g) (hwin g)
    rwa [hsq] at h
  refine ⟨{
    template := F
    vec := w
    vec_eq_zero := hsupp
    mass_lower := ?_
    mass_upper := ?_
    vec_close := ?_ }⟩
  · intro g
    have h := abs_le.mp (hmassabs g)
    linarith [h.1, h.2, hδhalf]
  · intro g
    have h := abs_le.mp (hmassabs g)
    linarith [h.1, h.2, hδhalf]
  · intro g h hgh S hSg hSh
    have hA := happ g g S hSg hSg
    have hB := happ h h S hSh hSh
    have hAB := happ g h S hSg hSh
    rw [gaussianKernel_self] at hA
    rw [gaussianKernel_self] at hB
    have hstrip : 1 - gaussianKernel f κ g h ≤ κ * (C * (Rad : ℝ) + D) ^ 2 :=
      one_sub_gaussianKernel_le hC hD hb hκ.le Rad g h (hRad g h hgh)
    have hexp : ∑ x ∈ S, (w g x - w h x) ^ 2
        = (∑ x ∈ S, w g x * w g x) + (∑ x ∈ S, w h x * w h x)
          - 2 * (∑ x ∈ S, w g x * w h x) := by
      have hrw : ∀ x ∈ S, (w g x - w h x) ^ 2
          = w g x * w g x + w h x * w h x - 2 * (w g x * w h x) := by
        intro x _
        ring
      rw [Finset.sum_congr rfl hrw, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]
    rw [hexp]
    have h1 := abs_le.mp hA
    have h2 := abs_le.mp hB
    have h3 := abs_le.mp hAB
    have hsq0 : (0 : ℝ) ≤ ε ^ 2 := sq_nonneg ε
    linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, hstrip, hκP, hδeps, hsq0]

/-- **Guentner--Kaminker Theorem 3.2, group side.**  A finitely generated group
whose Hilbert space compression exceeds `1/2` has Yu's property A --- granted
the two steps this repository cannot prove, both named in the statement:

* `hschoenberg` --- Schoenberg's theorem, that the Gaussian of a negative type
  kernel is of positive type;
* `hroe` --- the operator step, that a positive type kernel which is normalised,
  symmetric, and has uniformly bounded rows with uniformly vanishing tails is
  approximable by finite width squares.  The four clauses of `hroe`'s hypothesis
  are exactly what `gaussianKernel_lemma35_inputs` proves from the compression
  hypothesis, so nothing about the geometry is being assumed here: what is
  assumed is Guentner--Kaminker's passage through `C*_u(Γ)`.

The crossover from property A to exactness of `C⋆_red(Γ)` is Ozawa's theorem
(their Proposition 3.3) and is not formalised; see `Analysis/CStarExactness.lean`
for the standing record of that gap. -/
theorem hasPropertyA_of_compressionExceeds_half {T : Finset G}
    (hT : WordMetric.IsSymmetricGeneratingSet (↑T : Set G))
    (hcomp : CompressionExceeds (↑T : Set G) (1 / 2) E)
    (hschoenberg : ∀ (f : G → E) (κ : ℝ), 0 < κ →
      IsPositiveDefiniteKernel (gaussianKernel f κ))
    (hroe : ∀ u : G → G → ℝ, IsPositiveDefiniteKernel u →
      (∀ s : G, u s s = 1) → (∀ s t : G, u s t = u t s) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ (s : G) (F : Finset G), ∑ t ∈ F, u s t ≤ C) →
      (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ (s : G) (F : Finset G),
        (∀ t ∈ F, N < WordMetric.wordDist (↑T : Set G) s t) → ∑ t ∈ F, u s t ≤ δ) →
      IsRoeSquareApproximable u) :
    HasPropertyA G := by
  obtain ⟨f, β, hβ, hlip, hcompf⟩ := hcomp
  obtain ⟨C, D, hC, hD, hb⟩ := hlip
  refine hasPropertyA_of_gaussianRoeApproximation hC hD hb ?_
  intro κ hκ
  obtain ⟨hdiag, hsymm, hschur, htails⟩ :=
    gaussianKernel_lemma35_inputs hT hβ hcompf hκ
  exact hroe _ (hschoenberg f κ hκ) hdiag hsymm hschur htails

end GuentnerKaminker
end GroupApproximation
