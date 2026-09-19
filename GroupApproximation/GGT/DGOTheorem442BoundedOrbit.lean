import GroupApproximation.GGT.ElementaryProjectionCriterion
import GroupApproximation.GGT.OsinTheorem54SeparatingCosets
import GroupApproximation.GGT.WPDElementaryEmbedding

/-!
# DGO Theorem 4.42: the bounded-orbit branch

The projection complex in Dahmani--Guirardel--Osin's Theorem 4.42 is needed
only when the peripheral orbit is unbounded.  This module proves the entire
conclusion, including inequality (41), for a uniformly bounded orbit without
using a literature proposition.

Take the relative base to be all of `G`.  Its relative Cayley graph has
diameter at most one, hence is hyperbolic.  If the `H`-orbit of `s` has diameter
at most `B`, choose `alpha = 1 / (B + 1)`.  A relative path of length zero ends
at `1`, where the displacement vanishes; every positive natural radius is at
least one, while `alpha * d(s,h s) < 1`.  This is exactly (41).

This branch is deliberately separate from the generic projection boundary.
For the elementary closure of a loxodromic element the orbit is unbounded, so
the theorem below cannot discharge the Osin route by a degenerate base.  It
does show formally that the remaining content of `DGOTheorem442` is the
unbounded-orbit projection construction, rather than cone-off bookkeeping or
the bounded case.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

section UniversalBase

variable {G : Type u} [Group G]

/-- The relative generating set with base all of `G` and one peripheral
subgroup.  This is the correct witness for the bounded-orbit branch. -/
def universalBaseRelGenSet (H : Subgroup G) : RelGenSet G Unit where
  base := Set.univ
  fam := fun _ => H
  symmetricGenerating := by
    refine ⟨?_, ?_⟩
    · intro x _hx
      exact Set.mem_union_left _ (Set.mem_univ x⁻¹)
    · rw [eq_top_iff]
      intro x _hx
      exact Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_univ x))

@[simp] theorem universalBaseRelGenSet_base (H : Subgroup G) :
    (universalBaseRelGenSet H).base = Set.univ := rfl

@[simp] theorem universalBaseRelGenSet_fam (H : Subgroup G) :
    (universalBaseRelGenSet H).fam = fun _ => H := rfl

/-- Every group element is a letter in the universal-base relative alphabet. -/
theorem mem_universalBaseRelGenSet_alphabet (H : Subgroup G) (g : G) :
    g ∈ (universalBaseRelGenSet H).alphabet.carrier :=
  Set.mem_union_left _ (Set.mem_univ g)

/-- The universal-base relative Cayley graph has diameter at most one. -/
theorem universalBaseRelGenSet_dist_le_one (H : Subgroup G)
    (x y : Cayley (universalBaseRelGenSet H).alphabet) :
    dist x y ≤ (1 : ℝ) := by
  have hnorm : wordNorm (universalBaseRelGenSet H).alphabet.carrier
      ((Cayley.val x)⁻¹ * Cayley.val y) ≤ 1 :=
    wordNorm_le_one_of_mem
      (mem_universalBaseRelGenSet_alphabet H ((Cayley.val x)⁻¹ * Cayley.val y))
  have hdist : wordDist (universalBaseRelGenSet H).alphabet.carrier
      (Cayley.val x) (Cayley.val y) ≤ 1 := hnorm
  rw [Cayley.dist_eq]
  exact_mod_cast hdist

/-- The hyperbolicity clause of DGO 4.42 for a bounded peripheral orbit. -/
theorem universalBaseRelGenSet_hyperbolic (H : Subgroup G) :
    IsHyperbolicSpace 1 (Cayley (universalBaseRelGenSet H).alphabet) :=
  isHyperbolicSpace_of_bounded (universalBaseRelGenSet_dist_le_one H)

end UniversalBase

section BoundedOrbit

variable {G : Type u} [Group G] {S : Type v} [PseudoMetricSpace S]
  [MulAction G S]

/-- A uniformly bounded peripheral orbit.  The nonnegative bound is included
so that the coefficient `1 / (B + 1)` in (41) is visibly positive. -/
def HasBoundedOrbitAt (H : Subgroup G) (s : S) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ h : G, h ∈ H → dist s (h • s) ≤ B

/-- A finite subgroup has a bounded orbit under any action.  The bound is the
sum of the finitely many nonnegative displacements, avoiding any compactness
or properness assumption on the ambient pseudo-metric space. -/
theorem hasBoundedOrbitAt_of_finite (H : Subgroup G) (s : S)
    (hfin : (H : Set G).Finite) : HasBoundedOrbitAt H s := by
  classical
  let B : ℝ := ∑ h ∈ hfin.toFinset, dist s (h • s)
  refine ⟨B, ?_, ?_⟩
  · exact Finset.sum_nonneg fun _ _ => dist_nonneg
  · intro h hh
    have hh' : h ∈ hfin.toFinset := by simpa using hh
    dsimp [B]
    exact Finset.single_le_sum
      (fun (g : G) (_hg : g ∈ hfin.toFinset) =>
        (dist_nonneg : 0 ≤ dist s (g • s))) hh'

/-- The trivial subgroup has orbit `{s}`, hence bound zero. -/
theorem hasBoundedOrbitAt_bot (s : S) :
    HasBoundedOrbitAt (⊥ : Subgroup G) s := by
  refine ⟨0, le_rfl, ?_⟩
  intro h hh
  have hh1 : h = 1 := Subgroup.mem_bot.mp hh
  subst h
  simp

/-- **DGO inequality (41) for the universal-base witness.**

At radius zero, `relBall_zero` forces `h = 1`.  At positive radius the natural
radius is at least one, while boundedness of the orbit and the choice
`alpha = 1 / (B + 1)` bound the left side by `B / (B + 1) < 1`. -/
theorem universalBaseRelGenSet_orbitLowerBound
    (H : Subgroup G) (s : S) {B : ℝ} (hB0 : 0 ≤ B)
    (hbounded : ∀ h : G, h ∈ H → dist s (h • s) ≤ B) :
    ∀ (n : ℕ) (h : G), h ∈ (universalBaseRelGenSet H).relBall () n →
      (1 / (B + 1)) * dist s (h • s) ≤ (n : ℝ) := by
  intro n h hh
  rcases n with _ | n
  · have hh1 : h = 1 := by
      have : h ∈ ({1} : Set G) := by
        rw [← RelGenSet.relBall_zero (universalBaseRelGenSet H) ()]
        exact hh
      exact Set.mem_singleton_iff.mp this
    subst h
    simp
  · have hhH : h ∈ H := (RelGenSet.mem_relBall.mp hh).1
    have hdist := hbounded h hhH
    have hden : 0 < B + 1 := by linarith
    have hfrac : (1 / (B + 1)) * dist s (h • s) ≤ 1 := by
      rw [one_div, inv_mul_le_one₀ hden]
      linarith
    exact hfrac.trans (by exact_mod_cast Nat.succ_pos n)

/-- **Maximality of the universal-base branch.**  If the universal-base
relative generating set satisfies (41) for any positive coefficient, then the
peripheral orbit is bounded.

Indeed every `h ∈ H` is also a base letter, hence belongs to the relative
ball of radius one.  Inequality (41) therefore bounds every displacement by
`1 / alpha`.  This is why the universal base cannot handle the elementary
closure of a loxodromic element. -/
theorem hasBoundedOrbitAt_of_universalBaseRelGenSet_orbitLowerBound
    (H : Subgroup G) (s : S) {α : ℝ} (hα : 0 < α)
    (hlow : ∀ (n : ℕ) (h : G),
      h ∈ (universalBaseRelGenSet H).relBall () n →
        α * dist s (h • s) ≤ (n : ℝ)) :
    HasBoundedOrbitAt H s := by
  refine ⟨1 / α, (one_div_pos.mpr hα).le, ?_⟩
  intro h hh
  have hball : h ∈ (universalBaseRelGenSet H).relBall () 1 :=
    OsinComponents.mem_relBall_of_mem_base
      (universalBaseRelGenSet H) () hh (Set.mem_univ h)
  have hkey := hlow 1 h hball
  rw [le_div_iff₀ hα]
  simpa [mul_comm] using hkey

/-- The universal-base relative generating set satisfies DGO inequality (41)
for some positive coefficient **if and only if** the peripheral orbit is
bounded.  Thus the construction above is the complete universal-base branch,
not merely a sufficient special case. -/
theorem exists_universalBaseRelGenSet_orbitLowerBound_iff
    (H : Subgroup G) (s : S) :
    (∃ α : ℝ, 0 < α ∧ ∀ (n : ℕ) (h : G),
      h ∈ (universalBaseRelGenSet H).relBall () n →
        α * dist s (h • s) ≤ (n : ℝ)) ↔
      HasBoundedOrbitAt H s := by
  constructor
  · rintro ⟨α, hα, hlow⟩
    exact hasBoundedOrbitAt_of_universalBaseRelGenSet_orbitLowerBound H s hα hlow
  · rintro ⟨B, hB0, hB⟩
    refine ⟨1 / (B + 1), by positivity, ?_⟩
    exact universalBaseRelGenSet_orbitLowerBound H s hB0 hB

/-- **The exact output of DGO Theorem 4.42 for a bounded orbit.**

Neither quasiconvexity nor geometric separation is needed in this branch.  The
result nevertheless has precisely the existential output used by
`DGOTheorem442`, with a positive coefficient and inequality (41). -/
theorem exists_dgoTheorem442Output_of_boundedOrbit
    (H : Subgroup G) (s : S) (hbounded : HasBoundedOrbitAt H s) :
    ∃ (D : RelGenSet G Unit) (α : ℝ), 0 < α ∧
      D.fam = (fun _ => H) ∧
      (∃ δ' : ℝ, IsHyperbolicSpace δ' (Cayley D.alphabet)) ∧
      ∀ (n : ℕ) (h : G), h ∈ D.relBall () n →
        α * dist s (h • s) ≤ (n : ℝ) := by
  obtain ⟨B, hB0, hB⟩ := hbounded
  refine ⟨universalBaseRelGenSet H, 1 / (B + 1), ?_, rfl,
    ⟨1, universalBaseRelGenSet_hyperbolic H⟩, ?_⟩
  · positivity
  · exact universalBaseRelGenSet_orbitLowerBound H s hB0 hB

/-- Finite peripherals satisfy the exact DGO 4.42 output without a projection
complex. -/
theorem exists_dgoTheorem442Output_of_finite
    (H : Subgroup G) (s : S) (hfin : (H : Set G).Finite) :
    ∃ (D : RelGenSet G Unit) (α : ℝ), 0 < α ∧
      D.fam = (fun _ => H) ∧
      (∃ δ' : ℝ, IsHyperbolicSpace δ' (Cayley D.alphabet)) ∧
      ∀ (n : ℕ) (h : G), h ∈ D.relBall () n →
        α * dist s (h • s) ≤ (n : ℝ) :=
  exists_dgoTheorem442Output_of_boundedOrbit H s
    (hasBoundedOrbitAt_of_finite H s hfin)

/-- The trivial peripheral satisfies the exact DGO 4.42 output with bound zero
and coefficient one. -/
theorem exists_dgoTheorem442Output_bot (s : S) :
    ∃ (D : RelGenSet G Unit) (α : ℝ), 0 < α ∧
      D.fam = (fun _ => (⊥ : Subgroup G)) ∧
      (∃ δ' : ℝ, IsHyperbolicSpace δ' (Cayley D.alphabet)) ∧
      ∀ (n : ℕ) (h : G), h ∈ D.relBall () n →
        α * dist s (h • s) ≤ (n : ℝ) :=
  exists_dgoTheorem442Output_of_boundedOrbit ⊥ s (hasBoundedOrbitAt_bot s)

/-- The bounded-orbit restriction of DGO Theorem 4.42 is an unconditional
theorem of the development.  This mirrors the quantifier order of
`DGOTheorem442`, but adds exactly the boundedness hypothesis that makes the
projection complex unnecessary. -/
theorem dgoTheorem442_boundedOrbit :
    ∀ (G : Type u) [Group G] (S : Type v) [PseudoMetricSpace S] [MulAction G S]
      (H : Subgroup G) (s : S) (δ : ℝ),
      IsIsometricAction G S → IsHyperbolicSpace δ S → IsGeodesicSpace S →
        IsQuasiconvexOrbitAt H s → GeometricallySeparatedAt H s →
          HasBoundedOrbitAt H s →
            ∃ (D : RelGenSet G Unit) (α : ℝ), 0 < α ∧
              D.fam = (fun _ => H) ∧
              (∃ δ' : ℝ, IsHyperbolicSpace δ' (Cayley D.alphabet)) ∧
              ∀ (n : ℕ) (h : G), h ∈ D.relBall () n →
                α * dist s (h • s) ≤ (n : ℝ) := by
  intro G _ S _ _ H s _δ _hiso _hhyp _hgeo _hqc _hsep hbounded
  exact exists_dgoTheorem442Output_of_boundedOrbit H s hbounded

end BoundedOrbit

end Elementary
end GGT
end GroupApproximation
