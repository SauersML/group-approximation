import GroupApproximation.Analysis.CStarStandardModuleEquiv

/-!
# Truncation in `H_B`, countably generated modules, and stabilization

Kasparov's stabilization theorem --- `H_B ⊕ E ≅ H_B` for every countably
generated Hilbert `B`-module `E` --- is the theorem that makes `KK(A,B)` a
*group*: the inverse of a cycle is built by absorbing its module into the
standard one.  `Analysis.CStarStandardModuleEquiv` proved the case `E = H_B`.
This file states the general case, and proves the one lemma about `H_B` that
every approach to it starts from.

## What is proved

`truncate` and `exists_truncate_norm_le`: **every vector of `H_B` is
approximated in norm by a finitely supported one**.  This is not formal.  The
inner product of the tail is a `tsum`, and bounding it needs the Cauchy
criterion (`summable_iff_vanishing_norm`) together with the fact that a norm
bound on all partial sums passes to the limit --- which is where completeness
of `B` and continuity of the norm enter.  It is the statement that the
finitely supported sequences are dense in `H_B`, and it is the first step of
the Mingo--Phillips proof of stabilization as well as of the proof that `H_B`
is countably generated when `B` is separable.

## What is stated and not proved

`StabilizationInput`.  Two remarks about it.

* It is stated for modules whose carrier lies in the same universe as `B`,
  because a structure field cannot quantify over universes.  Every module this
  development builds --- `H_B`, direct sums of copies of it, submodules ---
  satisfies that.
* `stabilization_self` records that its conclusion is *already proved* for
  `E = H_B`.  That is not a proof of the input; it is the check that the input
  is not vacuous, and it locates precisely what is missing: the passage from
  the standard module to an arbitrary countably generated one.
-/

namespace GroupApproximation
namespace HilbertModule

open OrderZero Filter Topology

universe u v w

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B]

/-! ## Truncation -/

open scoped Classical in
/-- The truncation of a square-summable sequence to a finite set of
coordinates. -/
noncomputable def truncate {ι : Type u} (s : Finset ι) (f : ↥(summableSubmodule ι B)) :
    ↥(summableSubmodule ι B) :=
  ⟨fun i => if i ∈ s then f.1 i else 0, by
    refine summable_of_nonneg_of_le (fun i => ?_) (fun i => ?_) (summable_coe f)
    · by_cases h : i ∈ s <;> simp [h, star_mul_self_nonneg]
    · by_cases h : i ∈ s <;> simp [h, star_mul_self_nonneg]⟩

theorem truncate_coe_of_mem {ι : Type u} {s : Finset ι}
    {f : ↥(summableSubmodule ι B)} {i : ι} (h : i ∈ s) :
    (truncate s f).1 i = f.1 i := by
  simp [truncate, h]

theorem truncate_coe_of_not_mem {ι : Type u} {s : Finset ι}
    {f : ↥(summableSubmodule ι B)} {i : ι} (h : i ∉ s) :
    (truncate s f).1 i = 0 := by
  simp [truncate, h]

theorem sub_truncate_coe_of_mem {ι : Type u} {s : Finset ι}
    {f : ↥(summableSubmodule ι B)} {i : ι} (h : i ∈ s) :
    (f - truncate s f).1 i = 0 := by
  show f.1 i - (truncate s f).1 i = 0
  rw [truncate_coe_of_mem h, sub_self]

theorem sub_truncate_coe_of_not_mem {ι : Type u} {s : Finset ι}
    {f : ↥(summableSubmodule ι B)} {i : ι} (h : i ∉ s) :
    (f - truncate s f).1 i = f.1 i := by
  show f.1 i - (truncate s f).1 i = f.1 i
  rw [truncate_coe_of_not_mem h, sub_zero]

/-- **The finitely supported sequences are dense in `H_B`.**

The tail inner product is bounded on every finite partial sum by the Cauchy
criterion, and the bound passes to the limit because the norm is continuous
and `B` is complete. -/
theorem exists_truncate_norm_le {ι : Type u} (f : ↥(summableSubmodule ι B))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ι, (standardModule ι B).norm (f - truncate s f) ≤ ε := by
  classical
  obtain ⟨s, hs⟩ :=
    summable_iff_vanishing_norm.mp (summable_coe f) (ε ^ 2) (by positivity)
  refine ⟨s, ?_⟩
  have hgsum : Summable (fun i =>
      star ((f - truncate s f).1 i) * (f - truncate s f).1 i) :=
    summable_coe (f - truncate s f)
  have hpartial : ∀ t : Finset ι,
      ‖∑ i ∈ t, star ((f - truncate s f).1 i) * (f - truncate s f).1 i‖
        ≤ ε ^ 2 := by
    intro t
    have h1 : (∑ i ∈ t \ s,
          star ((f - truncate s f).1 i) * (f - truncate s f).1 i)
        = ∑ i ∈ t, star ((f - truncate s f).1 i) * (f - truncate s f).1 i := by
      refine Finset.sum_subset Finset.sdiff_subset fun i hi hni => ?_
      have hmem : i ∈ s := by
        by_contra hs'
        exact hni (Finset.mem_sdiff.mpr ⟨hi, hs'⟩)
      show star ((f - truncate s f).1 i) * (f - truncate s f).1 i = 0
      rw [sub_truncate_coe_of_mem hmem, star_zero, zero_mul]
    have h2 : (∑ i ∈ t \ s,
          star ((f - truncate s f).1 i) * (f - truncate s f).1 i)
        = ∑ i ∈ t \ s, star (f.1 i) * f.1 i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hmem : i ∉ s := (Finset.mem_sdiff.mp hi).2
      show star ((f - truncate s f).1 i) * (f - truncate s f).1 i
          = star (f.1 i) * f.1 i
      rw [sub_truncate_coe_of_not_mem hmem]
    rw [← h1, h2]
    exact le_of_lt (hs (t \ s) Finset.sdiff_disjoint)
  have htend0 : Tendsto (fun t : Finset ι =>
      ∑ i ∈ t, star ((f - truncate s f).1 i) * (f - truncate s f).1 i) atTop
      (𝓝 (∑' i, star ((f - truncate s f).1 i) * (f - truncate s f).1 i)) :=
    hgsum.hasSum
  have hlim : ‖∑' i,
      star ((f - truncate s f).1 i) * (f - truncate s f).1 i‖ ≤ ε ^ 2 :=
    le_of_tendsto htend0.norm (Eventually.of_forall hpartial)
  rw [standardModule_norm]
  calc Real.sqrt ‖∑' i, star ((f - truncate s f).1 i) * (f - truncate s f).1 i‖
      ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hlim
    _ = ε := Real.sqrt_sq hε.le

/-! ## Countably generated modules -/

/-- **A countably generated Hilbert module**: one with a sequence whose finite
`B`-combinations are dense. -/
def IsCountablyGenerated (E : CStarModule.{v, w} B) : Prop :=
  ∃ x : ℕ → E.carrier, ∀ (y : E.carrier) (ε : ℝ), 0 < ε →
    ∃ (n : ℕ) (b : Fin n → B) (k : Fin n → ℕ),
      E.norm (y - ∑ j, E.act (x (k j)) (b j)) ≤ ε

/-! ## Stabilization -/

/-- **Kasparov's stabilization theorem**, as an input: the standard module
absorbs every countably generated module.

Kasparov, *The operator K-functor and extensions of C⋆-algebras* (1980),
Theorem 2; the proof used here would be Mingo--Phillips.  It is stated for
carriers in the universe of `B` because a structure field cannot quantify over
universes, and every module built in this development satisfies that. -/
structure StabilizationInput (B : Type v) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] : Prop where
  /-- `H_B ⊕ E ≅ H_B` for countably generated `E`. -/
  absorbs : ∀ E : CStarModule.{v, v} B, IsCountablyGenerated E →
    ∃ U : Adjointable (prod (standardModule ℕ B) E) (standardModule ℕ B),
      U.IsUnitaryAdj

/-- **The conclusion of stabilization, proved for `E = H_B`.**

This is `natSumMerge`, and it is what makes `StabilizationInput` a statement
about the passage from `H_B` to a general countably generated module rather
than about absorption as such. -/
theorem stabilization_self (B : Type v) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] :
    ∃ U : Adjointable (prod (standardModule ℕ B) (standardModule ℕ B))
      (standardModule ℕ B), U.IsUnitaryAdj :=
  ⟨Adjointable.natSumMerge B, Adjointable.isUnitaryAdj_natSumMerge B⟩

end HilbertModule
end GroupApproximation
