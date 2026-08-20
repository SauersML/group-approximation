import GroupApproximation.Algebra.HyperbolicGroup
import GroupApproximation.Algebra.WordMetricComparison

/-!
# Betweenness, slim triangles, and the comparison that is still open

**This module is not imported by `GroupApproximation.lean`.**  It is authored
ahead of a build, and the two open comparisons it names are recorded as
`Prop`-valued definitions rather than as theorems, so nothing here asserts what
it does not prove.

## Betweenness

`IsBetween S b p c` says `d(b,p) + d(p,c) = d(b,c)`: in a geodesic space this is
exactly "`p` lies on some geodesic from `b` to `c`", and in the word metric it is
the statement that no route from `b` to `c` through `p` wastes a letter.
`exists_isBetween` produces such a `p` at every prescribed distance, by cutting a
geodesic word --- this is where `Algebra/WordMetricComparison.lean`'s subword
property is used, and it is what makes the Cayley graph a *geodesic* space in
the only sense this development needs.

## The Gromov product from below

`twiceGromovProduct_le_of_isBetween` is the elementary half of the comparison
between Gromov products and distances to geodesics: every point of a geodesic
from `b` to `c` is at least `(b·c)_a` away from `a`.  It is three triangle
inequalities and no geometry, and it is the first lemma of any proof of the
equivalences below.

## What is still open

`SlimImpliesFourPoint` and `FourPointImpliesSlim` are the two halves of the
standard equivalence between `δ`-slim triangles and Gromov's four-point
condition (Bridson and Haefliger, Part III.H; Ghys and de la Harpe).  Both need
the other half of the comparison --- that a point of `[a,b]` at distance
`(b·c)_a` from `a` is uniformly close to `[b,c]` --- which is the geometric
input this file does not have.  They are stated so that the gap is a named
object, and nothing in this repository is conditional on either.
-/

namespace GroupApproximation
namespace Hyperbolic

open WordMetric

universe u

variable {G : Type u} [Group G]

/-! ## A missing list lemma, derived from the two that are available -/

/-- The length of an initial segment, below the total length. -/
theorem length_take_of_le {l : List G} {i : ℕ} (hi : i ≤ l.length) :
    (l.take i).length = i := by
  have hsplit : (l.take i).length + (l.drop i).length = l.length := by
    rw [← List.length_append, List.take_append_drop]
  have hdrop : (l.drop i).length = l.length - i := List.length_drop
  omega

/-! ## Betweenness -/

/-- `p` lies **between** `b` and `c`: the route through `p` wastes nothing.  In a
geodesic space this says exactly that `p` is on some geodesic from `b` to `c`. -/
def IsBetween (S : Set G) (b p c : G) : Prop :=
  wordDist S b p + wordDist S p c = wordDist S b c

/-- An endpoint is between. -/
theorem isBetween_left (S : Set G) (b c : G) : IsBetween S b b c := by
  unfold IsBetween
  rw [wordDist_self]
  omega

/-- The other endpoint is between. -/
theorem isBetween_right {S : Set G} (b c : G) : IsBetween S b c c := by
  unfold IsBetween
  rw [wordDist_self]
  omega

/-- **Cutting a geodesic word produces a point between its endpoints.**  The
initial segment lands at distance `l₁.length`, and the remaining letters spell
the rest of the way. -/
theorem isBetween_of_geodesic_append {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {l₁ l₂ : List G} (b : G) (h : IsGeodesicWord S (l₁ ++ l₂) (l₁ ++ l₂).prod) :
    IsBetween S b (b * l₁.prod) (b * (l₁ ++ l₂).prod) ∧
      wordDist S b (b * l₁.prod) = l₁.length := by
  have hleft : IsWord S l₁ l₁.prod :=
    ⟨fun x hx => h.isWord.letters x (List.mem_append_left _ hx), rfl⟩
  have hgeoleft : wordNorm S l₁.prod = l₁.length := by
    have hcut := wordNorm_prod_take hS h l₁.length
    rw [List.take_left] at hcut
    omega
  have hb : wordDist S b (b * l₁.prod) = wordNorm S l₁.prod := by
    show wordNorm S (b⁻¹ * (b * l₁.prod)) = wordNorm S l₁.prod
    rw [inv_mul_cancel_left]
  have hmid : wordDist S (b * l₁.prod) (b * (l₁ ++ l₂).prod) = l₂.length := by
    rw [wordDist_left_invariant]
    exact wordDist_prod_append hS h
  have hwhole : wordDist S b (b * (l₁ ++ l₂).prod) = (l₁ ++ l₂).length := by
    show wordNorm S (b⁻¹ * (b * (l₁ ++ l₂).prod)) = (l₁ ++ l₂).length
    rw [inv_mul_cancel_left, ← h.length_eq]
  refine ⟨?_, ?_⟩
  · unfold IsBetween
    rw [hb, hgeoleft, hmid, hwhole, List.length_append]
  · rw [hb, hgeoleft]

/-- **Points at every prescribed distance lie between.**  The Cayley graph of a
group with a finite symmetric generating set is a geodesic space in this
sense. -/
theorem exists_isBetween {S : Set G} (hS : IsSymmetricGeneratingSet S) (b c : G)
    {i : ℕ} (hi : i ≤ wordDist S b c) :
    ∃ p : G, IsBetween S b p c ∧ wordDist S b p = i := by
  obtain ⟨l, hl⟩ := exists_isGeodesicWord hS (b⁻¹ * c)
  have hlen : l.length = wordDist S b c := hl.length_eq
  have hle : i ≤ l.length := by omega
  have hsplit : l.take i ++ l.drop i = l := List.take_append_drop i l
  have hgeo : IsGeodesicWord S l l.prod := by
    refine ⟨⟨hl.isWord.letters, rfl⟩, ?_⟩
    rw [hl.isWord.prod_eq]
    exact hl.length_eq
  have hgeo' : IsGeodesicWord S (l.take i ++ l.drop i) (l.take i ++ l.drop i).prod := by
    rw [hsplit]
    exact hgeo
  obtain ⟨hbetween, hdist⟩ := isBetween_of_geodesic_append hS b hgeo'
  have hc : b * (l.take i ++ l.drop i).prod = c := by
    rw [hsplit, hl.isWord.prod_eq, mul_inv_cancel_left]
  rw [hc] at hbetween
  refine ⟨b * (l.take i).prod, hbetween, ?_⟩
  rw [hdist, length_take_of_le hle]

/-! ## The Gromov product from below -/

/-- **A point between `b` and `c` is at least `(b·c)_a` from `a`.**  Three
triangle inequalities: `d(a,b) ≤ d(a,p) + d(p,b)`, `d(a,c) ≤ d(a,p) + d(p,c)`,
and the betweenness equation, added. -/
theorem twiceGromovProduct_le_of_isBetween {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (a : G) {b p c : G} (hp : IsBetween S b p c) :
    twiceGromovProduct S a b c ≤ 2 * (wordDist S a p : ℤ) := by
  have h₁ := wordDist_triangle hS a p b
  have h₂ := wordDist_triangle hS a p c
  have hpb := wordDist_comm hS p b
  have hbetween : wordDist S b p + wordDist S p c = wordDist S b c := hp
  simp only [twiceGromovProduct]
  omega

/-! ## Slim triangles -/

/-- **`δ`-slim triangles**: every point between two vertices is within `δ` of a
point between one of them and the third.  Sides are described by betweenness
rather than by chosen paths, which is what makes the condition stateable without
a metric-space structure on the Cayley graph. -/
def IsSlimTriangles (S : Set G) (δ : ℕ) : Prop :=
  ∀ x y z p : G, IsBetween S x p y →
    (∃ q : G, IsBetween S x q z ∧ wordDist S p q ≤ δ) ∨
      (∃ q : G, IsBetween S z q y ∧ wordDist S p q ≤ δ)

/-- Slimness only weakens as the constant grows. -/
theorem IsSlimTriangles.mono {S : Set G} {δ δ' : ℕ} (hδ : δ ≤ δ')
    (h : IsSlimTriangles S δ) : IsSlimTriangles S δ' := by
  intro x y z p hp
  rcases h x y z p hp with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
  · exact Or.inl ⟨q, hq, le_trans hd hδ⟩
  · exact Or.inr ⟨q, hq, le_trans hd hδ⟩

/-- **A bounded word metric has slim triangles**, with the bound as the
constant: the vertex `x` is on every side through `x`, and nothing is further
than `B` from it. -/
theorem isSlimTriangles_of_bounded {S : Set G} {B : ℕ}
    (hB : ∀ x y : G, wordDist S x y ≤ B) : IsSlimTriangles S B := by
  intro x y z p _
  exact Or.inl ⟨x, isBetween_left S x z, hB p x⟩

/-! ## The two open comparisons -/

/-- **Open.**  Slim triangles imply Gromov's four-point condition.  This is the
direction that turns a picture into an inequality; the proof compares the
Gromov product `(b·c)_a` with the distance from `a` to a side, and
`twiceGromovProduct_le_of_isBetween` is one of its two halves.  Not proved
here, and nothing in this repository assumes it. -/
def SlimImpliesFourPoint : Prop :=
  ∀ (H : Type) (_ : Group H) (S : Set H) (δ : ℕ),
    IsSymmetricGeneratingSet S → IsSlimTriangles S δ →
      ∃ δ' : ℕ, IsFourPointHyperbolic S δ'

/-- **Open.**  Gromov's four-point condition implies slim triangles.  This is
the harder direction of the classical equivalence, proved for geodesic spaces by
the tripod comparison (Bridson and Haefliger, Part III.H).  Not proved here, and
nothing in this repository assumes it. -/
def FourPointImpliesSlim : Prop :=
  ∀ (H : Type) (_ : Group H) (S : Set H) (δ : ℕ),
    IsSymmetricGeneratingSet S → IsFourPointHyperbolic S δ →
      ∃ δ' : ℕ, IsSlimTriangles S δ'

end Hyperbolic
end GroupApproximation
