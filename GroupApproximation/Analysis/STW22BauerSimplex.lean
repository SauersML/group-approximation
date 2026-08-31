import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.NNReal.Basic

/-!
# Choquet simplices, Bauer simplices, and transport of the extreme boundary

This file gives the two convexity definitions used by the STW Problem XXII
counterexample audit (`research/artifacts/stw22-trace-problem-counterexample-audit-2026-08-31.md`,
step (A6)) and proves the transport principle that the audit's identification
`T(A) ≅ Prob(K)` is used through.

## The definitional choices

* **Choquet simplex.**  A compact convex set `S` is a simplex, in the sense of
  Choquet, exactly when the cone over `S` is a *lattice cone*: the order that
  the cone induces on the group it generates is a lattice.  Since Mathlib has no
  Choquet theory at all, the condition is transcribed directly, in the form that
  needs no subtraction and therefore makes sense over an arbitrary ordered
  semiring of scalars:

  - `coneOver 𝕜 S ⊆ E × 𝕜` is the set of pairs `(t • x, t)` with `0 ≤ t`, `x ∈ S`;
  - `coneLE C u v` is `∃ c ∈ C, v = u + c`, the preorder a cone `C` induces;
  - `IsChoquetSimplex 𝕜 S` says every pair of elements of `coneOver 𝕜 S` has a
    least upper bound **inside the cone** for that preorder.

  Restricting the lattice condition to the cone itself is the standard
  formulation: a cone is a lattice cone iff every pair of its elements has a
  supremum in it, the general case following by translation.

* **Bauer simplex.**  `IsBauerSimplex 𝕜 S` is `IsChoquetSimplex 𝕜 S` together
  with `IsCompactConvexClosedBoundary 𝕜 S`, i.e. `S` compact and convex with
  *closed extreme boundary*.  The extreme boundary is Mathlib's
  `Set.extremePoints`; nothing about it is re-invented here.

  The two clauses are kept apart deliberately.  For the trace simplex of a
  C⋆-algebra the Choquet clause is classical and unformalisable at the present
  state of Mathlib, whereas the closed-boundary clause is exactly what the audit
  computes, and it is proved unconditionally for probability simplices in
  `Analysis/STW22ProbabilitySimplexBauer`.

## Why the scalars are left general

The set the audit needs this for is a set of *measures*, which form a module
over `ℝ≥0` and not over `ℝ` — there is no negation available.  Every definition
below is therefore stated over an arbitrary `[Semiring 𝕜] [PartialOrder 𝕜]`, and
instantiated at `𝕜 = ℝ≥0`.  On a set contained in a cone the notions of extreme
point over `ℝ≥0` and over `ℝ` agree, because `openSegment` only ever uses
strictly positive coefficients summing to one.

## Model test

`isChoquetSimplex_singleton` and `isBauerSimplex_singleton` verify that a
one-point set — a C⋆-algebra with a unique trace — is a Bauer simplex under
these definitions, with the lattice structure on its cone computed explicitly
(the supremum of `(t • x, t)` and `(s • x, s)` is `(max t s • x, max t s)`).
This is a genuine test: the least-upper-bound clause is discharged from the
cone data, not by unfolding a triviality.
-/

namespace GroupApproximation
namespace STW22

open Set

set_option linter.unusedSectionVars false

/-! ## The cone over a set, and the order it induces -/

section Cone

variable (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddCommMonoid E] [SMul 𝕜 E]

/-- The **cone over `S`**: the set of pairs `(t • x, t)` in `E × 𝕜` with `0 ≤ t`
and `x ∈ S`.  For `S` a compact convex set this is the cone whose lattice
property is Choquet's simplex condition. -/
def coneOver (S : Set E) : Set (E × 𝕜) :=
  {p : E × 𝕜 | ∃ t : 𝕜, ∃ x ∈ S, 0 ≤ t ∧ p = (t • x, t)}

/-- The preorder a cone `C` induces: `u ≤ v` when `v` is `u` translated by an
element of `C`.  Written with `+` rather than `-` so that it makes sense in an
additive monoid. -/
def coneLE (C : Set (E × 𝕜)) (u v : E × 𝕜) : Prop := ∃ c ∈ C, v = u + c

variable {𝕜}

theorem mem_coneOver {S : Set E} {p : E × 𝕜} :
    p ∈ coneOver 𝕜 S ↔ ∃ t : 𝕜, ∃ x ∈ S, 0 ≤ t ∧ p = (t • x, t) := Iff.rfl

theorem mk_mem_coneOver {S : Set E} {x : E} (hx : x ∈ S) {t : 𝕜} (ht : 0 ≤ t) :
    ((t • x, t) : E × 𝕜) ∈ coneOver 𝕜 S := ⟨t, x, hx, ht, rfl⟩

theorem coneLE_refl (C : Set (E × 𝕜)) (hC : (0 : E × 𝕜) ∈ C) (u : E × 𝕜) :
    coneLE 𝕜 C u u := ⟨0, hC, (add_zero u).symm⟩

end Cone

/-! ## Choquet simplices -/

/-- **Choquet's simplex condition.**  Every pair of elements of the cone over
`S` has a least upper bound, inside the cone, for the order the cone induces.

This is the lattice-cone form of the definition; see the module docstring for
why it is stated on the cone rather than on the group the cone generates. -/
def IsChoquetSimplex (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type*} [AddCommMonoid E] [SMul 𝕜 E] (S : Set E) : Prop :=
  ∀ u ∈ coneOver 𝕜 S, ∀ v ∈ coneOver 𝕜 S,
    ∃ w ∈ coneOver 𝕜 S,
      coneLE 𝕜 (coneOver 𝕜 S) u w ∧ coneLE 𝕜 (coneOver 𝕜 S) v w ∧
        ∀ z ∈ coneOver 𝕜 S,
          coneLE 𝕜 (coneOver 𝕜 S) u z → coneLE 𝕜 (coneOver 𝕜 S) v z →
            coneLE 𝕜 (coneOver 𝕜 S) w z

/-- The empty set satisfies the simplex condition vacuously.  Recorded only to
pin down that the quantifiers run over the cone and not over `E × 𝕜`. -/
theorem isChoquetSimplex_empty (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type*} [AddCommMonoid E] [SMul 𝕜 E] :
    IsChoquetSimplex 𝕜 (∅ : Set E) := by
  intro u hu
  obtain ⟨_, _, hx, _, _⟩ := hu
  exact absurd hx (notMem_empty _)

/-! ## Compactness, convexity and a closed extreme boundary -/

/-- The three clauses of a Bauer simplex that do not mention the lattice
condition: `S` is convex, compact, and its extreme boundary is closed.

The audit's step (A6) — `∂ₑ T(A) = K` with `K` compact — is exactly a proof of
this predicate for the trace simplex. -/
structure IsCompactConvexClosedBoundary (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type*} [AddCommMonoid E] [SMul 𝕜 E] [TopologicalSpace E] (S : Set E) : Prop where
  /-- `S` is convex. -/
  convex : Convex 𝕜 S
  /-- `S` is compact. -/
  isCompact : IsCompact S
  /-- The extreme boundary of `S` is closed. -/
  isClosed_extremePoints : IsClosed (S.extremePoints 𝕜)

/-- **Bauer simplex**: a Choquet simplex whose extreme boundary is closed. -/
def IsBauerSimplex (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type*} [AddCommMonoid E] [SMul 𝕜 E] [TopologicalSpace E] (S : Set E) : Prop :=
  IsChoquetSimplex 𝕜 S ∧ IsCompactConvexClosedBoundary 𝕜 S

theorem IsBauerSimplex.choquet {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type*} [AddCommMonoid E] [SMul 𝕜 E] [TopologicalSpace E] {S : Set E}
    (h : IsBauerSimplex 𝕜 S) : IsChoquetSimplex 𝕜 S := h.1

theorem IsBauerSimplex.isClosed_extremePoints {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type*} [AddCommMonoid E] [SMul 𝕜 E] [TopologicalSpace E] {S : Set E}
    (h : IsBauerSimplex 𝕜 S) : IsClosed (S.extremePoints 𝕜) := h.2.isClosed_extremePoints

/-- A compact extreme boundary is a closed one, in a Hausdorff ambient space.
This is the shape in which the probability-simplex computation delivers the
Bauer clause: the extreme boundary is exhibited as a continuous image of a
compact space. -/
theorem isCompactConvexClosedBoundary_of_isCompact_extremePoints
    {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type*} [AddCommMonoid E] [SMul 𝕜 E] [TopologicalSpace E] [T2Space E] {S : Set E}
    (hconv : Convex 𝕜 S) (hcomp : IsCompact S) (hext : IsCompact (S.extremePoints 𝕜)) :
    IsCompactConvexClosedBoundary 𝕜 S :=
  ⟨hconv, hcomp, hext.isClosed⟩

/-! ## Transport along a linear injection

The audit identifies `T(A)` with `Prob(K)`.  What that identification supplies
is an injective map which preserves sums and nonnegative scalar multiples, and
which is continuous for the two weak topologies.  These lemmas say that every
clause of `IsCompactConvexClosedBoundary` travels along such a map, so a
computation performed on `Prob(K)` is a computation about `T(A)`.
-/

section Transport

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E F : Type*} [AddCommMonoid E] [SMul 𝕜 E] [AddCommMonoid F] [SMul 𝕜 F]

/-- A map preserving sums and scalar multiples carries open segments onto open
segments. -/
theorem image_openSegment_of_linear (e : E → F)
    (hadd : ∀ x y : E, e (x + y) = e x + e y)
    (hsmul : ∀ (c : 𝕜) (x : E), e (c • x) = c • e x) (x y : E) :
    e '' openSegment 𝕜 x y = openSegment 𝕜 (e x) (e y) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
    exact ⟨a, b, ha, hb, hab, by rw [hadd, hsmul, hsmul]⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    exact ⟨a • x + b • y, ⟨a, b, ha, hb, hab, rfl⟩, by rw [hadd, hsmul, hsmul]⟩

/-- The extreme boundary is carried onto the extreme boundary by an injective
map preserving sums and scalar multiples. -/
theorem extremePoints_image_of_linear (e : E → F) (hinj : Function.Injective e)
    (hadd : ∀ x y : E, e (x + y) = e x + e y)
    (hsmul : ∀ (c : 𝕜) (x : E), e (c • x) = c • e x) (S : Set E) :
    (e '' S).extremePoints 𝕜 = e '' (S.extremePoints 𝕜) := by
  have hseg : ∀ x y : E, e '' openSegment 𝕜 x y = openSegment 𝕜 (e x) (e y) :=
    image_openSegment_of_linear e hadd hsmul
  apply Set.Subset.antisymm
  · rintro z ⟨hzS, hz⟩
    obtain ⟨x, hxS, rfl⟩ := hzS
    refine ⟨x, ⟨hxS, ?_⟩, rfl⟩
    intro x₁ hx₁ x₂ hx₂ hmem
    have hmem' : e x ∈ openSegment 𝕜 (e x₁) (e x₂) := by
      rw [← hseg x₁ x₂]
      exact mem_image_of_mem e hmem
    have him₁ : e x₁ ∈ e '' S := mem_image_of_mem e hx₁
    have him₂ : e x₂ ∈ e '' S := mem_image_of_mem e hx₂
    exact hinj (hz him₁ him₂ hmem')
  · rintro _ ⟨x, ⟨hxS, hx⟩, rfl⟩
    refine ⟨mem_image_of_mem e hxS, ?_⟩
    intro y₁ hy₁ y₂ hy₂ hmem
    obtain ⟨x₁, hx₁, rfl⟩ := hy₁
    obtain ⟨x₂, hx₂, rfl⟩ := hy₂
    rw [← hseg x₁ x₂] at hmem
    obtain ⟨w, hw, hew⟩ := hmem
    have hxw : w = x := hinj hew
    rw [hxw] at hw
    exact congrArg e (hx hx₁ hx₂ hw)

/-- Every clause of `IsCompactConvexClosedBoundary` transports along a
continuous injective map preserving sums and scalar multiples. -/
theorem IsCompactConvexClosedBoundary.image [TopologicalSpace E] [TopologicalSpace F] [T2Space F]
    {S : Set E} (h : IsCompactConvexClosedBoundary 𝕜 S) (e : E → F)
    (hcont : Continuous e) (hinj : Function.Injective e)
    (hadd : ∀ x y : E, e (x + y) = e x + e y)
    (hsmul : ∀ (c : 𝕜) (x : E), e (c • x) = c • e x) :
    IsCompactConvexClosedBoundary 𝕜 (e '' S) where
  convex := by
    intro y₁ hy₁ y₂ hy₂ a b ha hb hab
    obtain ⟨x₁, hx₁, rfl⟩ := hy₁
    obtain ⟨x₂, hx₂, rfl⟩ := hy₂
    exact ⟨a • x₁ + b • x₂, h.convex hx₁ hx₂ ha hb hab, by rw [hadd, hsmul, hsmul]⟩
  isCompact := h.isCompact.image hcont
  isClosed_extremePoints := by
    rw [extremePoints_image_of_linear e hinj hadd hsmul S]
    exact ((h.isCompact.of_isClosed_subset h.isClosed_extremePoints
      extremePoints_subset).image hcont).isClosed

end Transport

/-! ## Model test: a single point is a Bauer simplex

A C⋆-algebra with exactly one tracial state has a one-point trace simplex, and
that is the smallest Bauer simplex.  The lattice condition is checked by hand
below, over `ℝ≥0`, which is the scalar ring the measure-theoretic instance uses.
-/

section Singleton

open scoped NNReal

variable {E : Type*} [AddCommMonoid E] [Module ℝ≥0 E]

/-- Every element of the cone over a singleton `{x}` is `(t • x, t)`. -/
theorem mem_coneOver_singleton {x : E} {p : E × ℝ≥0} :
    p ∈ coneOver ℝ≥0 ({x} : Set E) ↔ ∃ t : ℝ≥0, p = (t • x, t) := by
  constructor
  · rintro ⟨t, y, hy, -, rfl⟩
    rw [mem_singleton_iff] at hy
    subst hy
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact mk_mem_coneOver rfl (zero_le : (0 : ℝ≥0) ≤ t)

/-- Along the ray over a singleton, the induced order is the order of `ℝ≥0` on
the scalar coordinate. -/
theorem coneLE_singleton_iff {x : E} {t s : ℝ≥0} :
    coneLE ℝ≥0 (coneOver ℝ≥0 ({x} : Set E)) (t • x, t) (s • x, s) ↔ t ≤ s := by
  constructor
  · rintro ⟨c, hc, hcs⟩
    rw [mem_coneOver_singleton] at hc
    obtain ⟨a, rfl⟩ := hc
    have hsnd : s = t + a := congrArg Prod.snd hcs
    rw [hsnd]
    exact self_le_add_right t a
  · intro hts
    refine ⟨((s - t) • x, s - t), mk_mem_coneOver rfl (zero_le : (0 : ℝ≥0) ≤ s - t), ?_⟩
    have hadd : t + (s - t) = s := add_tsub_cancel_of_le hts
    apply Prod.ext
    · show s • x = t • x + (s - t) • x
      rw [← add_smul, hadd]
    · show s = t + (s - t)
      rw [hadd]

/-- **Model test.**  A one-point set is a Choquet simplex: the cone over it is
the ray `{(t • x, t)}`, on which the induced order is the linear order of `ℝ≥0`,
so binary suprema exist and are given by `max`. -/
theorem isChoquetSimplex_singleton (x : E) : IsChoquetSimplex ℝ≥0 ({x} : Set E) := by
  intro u hu v hv
  rw [mem_coneOver_singleton] at hu hv
  obtain ⟨t, rfl⟩ := hu
  obtain ⟨s, rfl⟩ := hv
  refine ⟨(max t s • x, max t s), mem_coneOver_singleton.mpr ⟨max t s, rfl⟩,
    coneLE_singleton_iff.mpr (le_max_left t s),
    coneLE_singleton_iff.mpr (le_max_right t s), ?_⟩
  intro z hz h₁ h₂
  rw [mem_coneOver_singleton] at hz
  obtain ⟨r, rfl⟩ := hz
  exact coneLE_singleton_iff.mpr
    (max_le (coneLE_singleton_iff.mp h₁) (coneLE_singleton_iff.mp h₂))

/-- **Model test.**  A one-point set is a Bauer simplex. -/
theorem isBauerSimplex_singleton [TopologicalSpace E] [T1Space E] (x : E) :
    IsBauerSimplex ℝ≥0 ({x} : Set E) := by
  refine ⟨isChoquetSimplex_singleton x, ?_, isCompact_singleton, ?_⟩
  · exact convex_singleton x
  · rw [extremePoints_singleton]
    exact isClosed_singleton

end Singleton

end STW22
end GroupApproximation
