import GroupApproximation.Analysis.CStarModuleDirectSum

/-!
# The standard module `H_B = ℓ²(B)`

The Hilbert module in which every countably generated Hilbert `B`-module sits:
the square-summable sequences over `B`, with `⟨f, g⟩ = ∑ᵢ f(i)⋆g(i)`.  It is
the module Kasparov's stabilization theorem is about (`H_B ⊕ E ≅ H_B`), hence
the module the inverse in `KK(A,B)` is built from.

## The two analytic facts

Everything here rests on two statements, and both are proved.

* **Domination.**  If `0 ≤ cᵢ ≤ dᵢ` and `∑dᵢ` converges, so does `∑cᵢ`.
  Positive series in a C⋆-algebra are *not* absolutely convergent in general
  --- `eᵢ/i` in `c₀` is the standard counterexample --- so this cannot be
  proved by comparison of norms of terms.  It is proved by the Cauchy
  criterion on finite subsets, where the comparison is of norms of *partial
  sums* and is legitimate because the norm is monotone on positives.
  This is what makes `H_B` closed under addition, via the parallelogram
  estimate `(f+g)⋆(f+g) ≤ 2(f⋆f + g⋆g)` of `Analysis.CStarPositiveOrder`.
* **Cross terms.**  If `∑fᵢ⋆fᵢ` and `∑gᵢ⋆gᵢ` converge then `∑fᵢ⋆gᵢ` converges.
  This is Cauchy--Schwarz **in the finite direct sum `B^s`**, one finite subset
  `s` at a time:
  `‖∑_{i∈s} fᵢ⋆gᵢ‖ ≤ ‖∑_{i∈s} fᵢ⋆fᵢ‖^{1/2}‖∑_{i∈s} gᵢ⋆gᵢ‖^{1/2}`, which is
  exactly `norm_inner_le` for the module `piSelf s B` of
  `Analysis.CStarModuleDirectSum`.  That is why the finite direct sum is built
  before the infinite one: it is not a special case of `H_B`, it is a lemma
  about `H_B`.

## What is proved

`summableSubmodule` --- the square-summable sequences as a `ℂ`-submodule of
`ι → B`, so that the additive and scalar structure of `H_B` is inherited
rather than constructed --- and `standardModule`, with all ten Hilbert-module
axioms discharged.  Definiteness is `le_hasSum`: a positive summand of a
vanishing sum of positives vanishes, and then the C⋆-identity finishes.

`ι` is arbitrary.  `H_B` proper is the countable case, and countability is
imposed by the theorems that need it (stabilization), not by the definition.
-/

namespace GroupApproximation
namespace HilbertModule

open OrderZero

universe u v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B]

/-! ## Domination -/

/-- **A dominated family of positive elements is summable.**

Not a comparison of norms of terms --- a summable family of positive elements
of a C⋆-algebra need not be absolutely summable --- but a comparison of norms
of partial sums, which is what the Cauchy criterion sees. -/
theorem summable_of_nonneg_of_le {ι : Type u} {c d : ι → B}
    (hc : ∀ i, 0 ≤ c i) (hcd : ∀ i, c i ≤ d i) (hd : Summable d) :
    Summable c := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hd ε hε
  refine ⟨s, fun t ht => ?_⟩
  have h1 : (0 : B) ≤ ∑ i ∈ t, c i := Finset.sum_nonneg fun i _ => hc i
  have h2 : (∑ i ∈ t, c i) ≤ ∑ i ∈ t, d i :=
    Finset.sum_le_sum fun i _ => hcd i
  exact lt_of_le_of_lt (OrderZero.norm_le_norm_of_nonneg_of_le h1 h2) (hs t ht)

/-! ## Cauchy--Schwarz over a finite subset -/

/-- **Cauchy--Schwarz for a finite partial sum.**

This is `norm_inner_le` for the module `B^s`; no new argument, only the
observation that the partial sums of two sequences are two vectors of a finite
direct sum. -/
theorem norm_sum_star_mul_le {ι : Type u} (s : Finset ι) (f g : ι → B) :
    ‖∑ i ∈ s, star (f i) * g i‖
      ≤ Real.sqrt ‖∑ i ∈ s, star (f i) * f i‖
        * Real.sqrt ‖∑ i ∈ s, star (g i) * g i‖ := by
  have h := (piSelf (↥s) B).norm_inner_le (fun i : ↥s => f (i : ι))
    (fun i : ↥s => g (i : ι))
  have hfg : (piSelf (↥s) B).inner (fun i : ↥s => f (i : ι))
    (fun i : ↥s => g (i : ι)) = ∑ i ∈ s, star (f i) * g i := by
    show (∑ i : ↥s, star (f (i : ι)) * g (i : ι)) = ∑ i ∈ s, star (f i) * g i
    rw [← Finset.sum_coe_sort s]
  have hff : (piSelf (↥s) B).norm (fun i : ↥s => f (i : ι))
      = Real.sqrt ‖∑ i ∈ s, star (f i) * f i‖ := by
    rw [CStarModule.norm_def]
    congr 1
    show ‖∑ i : ↥s, star (f (i : ι)) * f (i : ι)‖ = ‖∑ i ∈ s, star (f i) * f i‖
    rw [← Finset.sum_coe_sort s]
  have hgg : (piSelf (↥s) B).norm (fun i : ↥s => g (i : ι))
      = Real.sqrt ‖∑ i ∈ s, star (g i) * g i‖ := by
    rw [CStarModule.norm_def]
    congr 1
    show ‖∑ i : ↥s, star (g (i : ι)) * g (i : ι)‖ = ‖∑ i ∈ s, star (g i) * g i‖
    rw [← Finset.sum_coe_sort s]
  rw [hfg, hff, hgg] at h
  exact h

/-- **The cross terms of two square-summable sequences are summable.** -/
theorem summable_star_mul {ι : Type u} {f g : ι → B}
    (hf : Summable fun i => star (f i) * f i)
    (hg : Summable fun i => star (g i) * g i) :
    Summable fun i => star (f i) * g i := by
  classical
  rw [summable_iff_vanishing_norm]
  intro ε hε
  obtain ⟨s₁, h₁⟩ := summable_iff_vanishing_norm.mp hf ε hε
  obtain ⟨s₂, h₂⟩ := summable_iff_vanishing_norm.mp hg ε hε
  refine ⟨s₁ ∪ s₂, fun t ht => ?_⟩
  have hA := h₁ t (ht.mono_right Finset.subset_union_left)
  have hB := h₂ t (ht.mono_right Finset.subset_union_right)
  have hA0 : (0 : ℝ) ≤ ‖∑ i ∈ t, star (f i) * f i‖ := norm_nonneg _
  have hB0 : (0 : ℝ) ≤ ‖∑ i ∈ t, star (g i) * g i‖ := norm_nonneg _
  refine lt_of_le_of_lt (norm_sum_star_mul_le t f g) ?_
  calc Real.sqrt ‖∑ i ∈ t, star (f i) * f i‖
        * Real.sqrt ‖∑ i ∈ t, star (g i) * g i‖
      = Real.sqrt (‖∑ i ∈ t, star (f i) * f i‖
          * ‖∑ i ∈ t, star (g i) * g i‖) := (Real.sqrt_mul hA0 _).symm
    _ < Real.sqrt (ε * ε) := by
        refine (Real.sqrt_lt_sqrt_iff (by positivity)).mpr ?_
        nlinarith
    _ = ε := Real.sqrt_mul_self hε.le

/-! ## The square-summable sequences -/

/-- **The square-summable sequences**, as a `ℂ`-submodule of `ι → B`.

Closure under addition is the parallelogram estimate together with
`summable_of_nonneg_of_le`; closure under scalars is
`f⋆f ↦ (c̄c)·(f⋆f)`. -/
def summableSubmodule (ι : Type u) (B : Type v) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] : Submodule ℂ (ι → B) where
  carrier := {f | Summable fun i => star (f i) * f i}
  add_mem' {f g} hf hg := by
    have hf' : Summable fun i => star (f i) * f i := hf
    have hg' : Summable fun i => star (g i) * g i := hg
    refine summable_of_nonneg_of_le (fun i => star_mul_self_nonneg _)
      (fun i => ?_) ((hf'.add hg').add (hf'.add hg'))
    exact OrderZero.star_add_mul_self_le
  zero_mem' := by
    show Summable fun i : ι => star ((0 : ι → B) i) * (0 : ι → B) i
    simp
  smul_mem' c f hf := by
    have hf' : Summable fun i => star (f i) * f i := hf
    refine Summable.congr (hf'.const_smul (star c * c)) fun i => ?_
    show (star c * c) • (star (f i) * f i) = star (c • f i) * (c • f i)
    rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]

theorem summable_of_mem_summableSubmodule {ι : Type u} {f : ι → B}
    (hf : f ∈ summableSubmodule ι B) : Summable fun i => star (f i) * f i := hf

theorem summable_coe {ι : Type u} (f : ↥(summableSubmodule ι B)) :
    Summable fun i => star (f.1 i) * f.1 i := f.2

/-! ## The module -/

/-- **The standard module `H_B = ℓ²(B)`**, with `⟨f,g⟩ = ∑ᵢ f(i)⋆g(i)`.

Every clause about the inner product is a `tsum` identity, and every one of
them needs the cross terms to be summable, which is `summable_star_mul`. -/
noncomputable def standardModule (ι : Type u) (B : Type v) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] : CStarModule.{v, max u v} B where
  carrier := ↥(summableSubmodule ι B)
  act f b := ⟨fun i => f.1 i * b, by
    have hmap : Summable fun i => star b * (star (f.1 i) * f.1 i) * b := by
      have hcont : Continuous fun x : B => star b * x * b :=
        (continuous_const.mul continuous_id).mul continuous_const
      have h := (summable_coe f).map
        (AddMonoidHom.mk' (fun x : B => star b * x * b)
          (fun x y => by rw [mul_add, add_mul])) hcont
      exact h.congr fun i => rfl
    refine Summable.congr hmap fun i => ?_
    show star b * (star (f.1 i) * f.1 i) * b = star (f.1 i * b) * (f.1 i * b)
    rw [star_mul]
    simp only [mul_assoc]⟩
  inner f g := ∑' i, star (f.1 i) * g.1 i
  act_add_left f g b := by
    refine Subtype.ext (funext fun i => ?_)
    show (f.1 i + g.1 i) * b = f.1 i * b + g.1 i * b
    rw [add_mul]
  act_add_right f b c := by
    refine Subtype.ext (funext fun i => ?_)
    show f.1 i * (b + c) = f.1 i * b + f.1 i * c
    rw [mul_add]
  act_assoc f b c := by
    refine Subtype.ext (funext fun i => ?_)
    show f.1 i * b * c = f.1 i * (b * c)
    rw [mul_assoc]
  act_smul c f b := by
    refine Subtype.ext (funext fun i => ?_)
    show (c • f.1 i) * b = c • (f.1 i * b)
    rw [smul_mul_assoc]
  inner_add_right f g h := by
    show (∑' i, star (f.1 i) * (g.1 i + h.1 i))
        = (∑' i, star (f.1 i) * g.1 i) + ∑' i, star (f.1 i) * h.1 i
    rw [show (fun i => star (f.1 i) * (g.1 i + h.1 i))
        = (fun i => star (f.1 i) * g.1 i + star (f.1 i) * h.1 i) from
      funext fun i => mul_add _ _ _]
    exact (summable_star_mul (summable_coe f) (summable_coe g)).tsum_add
      (summable_star_mul (summable_coe f) (summable_coe h))
  inner_smul_right c f g := by
    show (∑' i, star (f.1 i) * (c • g.1 i)) = c • ∑' i, star (f.1 i) * g.1 i
    rw [show (fun i => star (f.1 i) * (c • g.1 i))
        = (fun i => c • (star (f.1 i) * g.1 i)) from
      funext fun i => mul_smul_comm _ _ _]
    exact (summable_star_mul (summable_coe f) (summable_coe g)).tsum_const_smul c
  inner_act_right f g b := by
    show (∑' i, star (f.1 i) * (g.1 i * b))
        = (∑' i, star (f.1 i) * g.1 i) * b
    rw [show (fun i => star (f.1 i) * (g.1 i * b))
        = (fun i => (star (f.1 i) * g.1 i) * b) from
      funext fun i => (mul_assoc _ _ _).symm]
    exact (summable_star_mul (summable_coe f) (summable_coe g)).tsum_mul_right b
  inner_star f g := by
    show star (∑' i, star (f.1 i) * g.1 i) = ∑' i, star (g.1 i) * f.1 i
    rw [tsum_star]
    refine tsum_congr fun i => ?_
    rw [star_mul, star_star]
  inner_self_isPositive f :=
    OrderZero.isPositiveElem_of_nonneg
      (tsum_nonneg fun i => star_mul_self_nonneg _)
  inner_self_eq_zero f hf := by
    have hzero : HasSum (fun i => star (f.1 i) * f.1 i) 0 := by
      have h := (summable_coe f).hasSum
      rwa [hf] at h
    refine Subtype.ext (funext fun i => ?_)
    have hle : star (f.1 i) * f.1 i ≤ 0 :=
      le_hasSum hzero i fun j _ => star_mul_self_nonneg _
    have heq : star (f.1 i) * f.1 i = 0 :=
      le_antisymm hle (star_mul_self_nonneg _)
    have hn : ‖f.1 i‖ * ‖f.1 i‖ = 0 := by
      rw [← CStarRing.norm_star_mul_self, heq, norm_zero]
    have hz : ‖f.1 i‖ = 0 := by nlinarith [norm_nonneg (f.1 i)]
    exact norm_eq_zero.mp hz

@[simp] theorem standardModule_inner {ι : Type u}
    (f g : ↥(summableSubmodule ι B)) :
    (standardModule ι B).inner f g = ∑' i, star (f.1 i) * g.1 i := rfl

@[simp] theorem standardModule_act {ι : Type u}
    (f : ↥(summableSubmodule ι B)) (b : B) :
    ((standardModule ι B).act f b).1 = fun i => f.1 i * b := rfl

/-- The norm of `H_B`: `‖f‖² = ‖∑ᵢ f(i)⋆f(i)‖`. -/
theorem standardModule_norm {ι : Type u} (f : ↥(summableSubmodule ι B)) :
    (standardModule ι B).norm f
      = Real.sqrt ‖∑' i, star (f.1 i) * f.1 i‖ := rfl

end HilbertModule
end GroupApproximation
