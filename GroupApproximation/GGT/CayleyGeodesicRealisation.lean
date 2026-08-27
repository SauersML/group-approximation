import GroupApproximation.GGT.CayleyGeodesicModel

/-!
# The realisation of `Γ(G,A)` is a geodesic space

`GGT.CayleyGeodesicModel` proves that the metric realisation of `Γ(G,A)` is
geodesic **between vertices** (`exists_vertexGeodesic`) and leaves
`IsGeodesicRealisation` — geodesicity between arbitrary points — as its one
residual.  This module discharges it.

## Only upper bounds are needed

The construction would be painful if each distance along the path had to be
computed exactly.  It does not:

> `isGeodesicSegment_of_lipschitz` — a path whose endpoints are as far apart as
> its length, and which is `1`-Lipschitz, is a geodesic segment.

The lower bound comes for free, from the triangle inequality against the two
endpoints: `d = d(γ 0, γ d) ≤ s + d(γ s, γ t) + (d - t)`.  So every estimate
below is an upper bound, and every upper bound in this space is either
`pointDist ≤ |Δparam|` on a shared edge or `pointDist ≤ viaVertex ≤ toVertex`
against a vertex.  Neither needs a case split.

## The path

For `p` and `q` at distance `d`:

* if they share an edge and `d` is `|p.param - q.param|`, the path moves the
  parameter linearly inside that edge (`Point.withParam`);
* otherwise `d = viaVertex p q`, which is `α + wordDist v w + ζ` for one of the
  four choices of an endpoint `v` of `p`'s edge and an endpoint `w` of `q`'s.
  The path retracts `p` to `v` inside its edge (`retractBase`, `retractTip`),
  crosses by `exists_vertexGeodesic`, and runs into `q` from `w`.

`exists_geodesic_of_split` is that three-piece assembly, stated once and applied
in each of the four cases; the case analysis is `pointDist_cases`, then
`viaVertex_cases`, then `toVertex_cases`, and in each leaf the length identity
`d = α + wordDist v w + ζ` is what those `cases` lemmas say.

## Endpoints on the nose

`IsGeodesicSpace` asks for `f 0 = p` and `f d = q` as equalities of points, not
merely at distance zero, which is why the retraction paths carry an `r ≤ 0`
branch returning `p` itself and a far branch snapping to the vertex.  `Point.ext'`
is what turns the parameter equation into an equality of points; the proof
fields of `Point` are propositions, so they take care of themselves.

## Status

**Not compiled.**  Written while builds were frozen, and not in the root import
list for that reason.
-/

namespace GroupApproximation
namespace GGT
namespace CayleyGeodesicModel

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open scoped Classical

universe u

variable {G : Type u} [Group G]

/-! ## A Lipschitz criterion for geodesic segments -/

/-- **A `1`-Lipschitz path whose endpoints are as far apart as its length is a
geodesic segment.**  The lower bound is the triangle inequality against the two
endpoints, and both of the bounds it needs are instances of the Lipschitz
hypothesis. -/
theorem isGeodesicSegment_of_lipschitz {X : Type*} [PseudoMetricSpace X]
    {γ : ℝ → X} {d : ℝ} (h0 : 0 ≤ d) (hd : dist (γ 0) (γ d) = d)
    (hup : ∀ s ∈ Set.Icc (0 : ℝ) d, ∀ t ∈ Set.Icc (0 : ℝ) d, s ≤ t →
      dist (γ s) (γ t) ≤ t - s) :
    IsGeodesicSegment γ 0 d := by
  have key : ∀ s ∈ Set.Icc (0 : ℝ) d, ∀ t ∈ Set.Icc (0 : ℝ) d, s ≤ t →
      dist (γ s) (γ t) = t - s := by
    intro s hs t ht hst
    have h1 : dist (γ 0) (γ s) ≤ s - 0 :=
      hup 0 ⟨le_refl 0, h0⟩ s hs hs.1
    have h2 : dist (γ t) (γ d) ≤ d - t :=
      hup t ht d ⟨h0, le_refl d⟩ ht.2
    have h3 : dist (γ 0) (γ d) ≤ dist (γ 0) (γ s) + dist (γ s) (γ d) :=
      dist_triangle _ _ _
    have h4 : dist (γ s) (γ d) ≤ dist (γ s) (γ t) + dist (γ t) (γ d) :=
      dist_triangle _ _ _
    have h5 := hup s hs t ht hst
    rw [hd] at h3
    linarith
  intro s hs t ht
  rcases le_total s t with h | h
  · rw [key s hs t ht h, abs_of_nonpos (by linarith)]
    ring
  · rw [dist_comm, key t ht s hs h, abs_of_nonneg (by linarith)]

/-! ## Moving inside one edge -/

namespace Point

variable {A : Alphabet G}

/-- Two points of the realisation with the same data are equal: the remaining
fields are proofs. -/
theorem ext' {p q : Point A} (hb : p.base = q.base) (hl : p.letter = q.letter)
    (hp : p.param = q.param) : p = q := by
  cases p
  cases q
  simp only at hb hl hp
  subst hb
  subst hl
  subst hp
  rfl

/-- The point of `p`'s edge at parameter `t`, clamped so that the definition is
total. -/
noncomputable def withParam (p : Point A) (t : ℝ) : Point A where
  base := p.base
  letter := p.letter
  letter_mem := p.letter_mem
  param := min 1 (max 0 t)
  param_nonneg := le_min (by norm_num) (le_max_left _ _)
  param_le_one := min_le_left _ _

@[simp] theorem withParam_base (p : Point A) (t : ℝ) :
    (p.withParam t).base = p.base := rfl

@[simp] theorem withParam_letter (p : Point A) (t : ℝ) :
    (p.withParam t).letter = p.letter := rfl

@[simp] theorem withParam_tip (p : Point A) (t : ℝ) :
    (p.withParam t).tip = p.tip := rfl

theorem withParam_param (p : Point A) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (p.withParam t).param = t := by
  show min 1 (max 0 t) = t
  rw [max_eq_right h0, min_eq_right h1]

theorem withParam_self (p : Point A) : p.withParam p.param = p :=
  ext' rfl rfl (withParam_param p p.param_nonneg p.param_le_one)

/-- Two points of one edge are at most the difference of their parameters
apart. -/
theorem dist_withParam_le (p : Point A) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    dist (p.withParam s) (p.withParam t) ≤ |s - t| := by
  show pointDist (p.withParam s) (p.withParam t) ≤ |s - t|
  unfold pointDist
  rw [if_pos ⟨rfl, rfl⟩]
  refine le_trans (min_le_left _ _) ?_
  rw [withParam_param p hs0 hs1, withParam_param p ht0 ht1]

/-- A point of an edge is at most its parameter from the base vertex. -/
theorem dist_withParam_base_le (p : Point A) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ 1) : dist (p.withParam t) (vertex A p.base) ≤ t := by
  have hle := pointDist_le_viaVertex (p.withParam t) (vertex A p.base)
  have hvia := viaVertex_vertex_right (p.withParam t) p.base
  have hbound := toVertex_le_base_add (p.withParam t) p.base
  rw [withParam_base, wordDist_self, withParam_param p h0 h1] at hbound
  push_cast at hbound
  show pointDist (p.withParam t) (vertex A p.base) ≤ t
  rw [hvia] at hle
  linarith

/-- A point of an edge is at most `1 -` its parameter from the far vertex. -/
theorem dist_withParam_tip_le (p : Point A) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ 1) : dist (p.withParam t) (vertex A p.tip) ≤ 1 - t := by
  have hle := pointDist_le_viaVertex (p.withParam t) (vertex A p.tip)
  have hvia := viaVertex_vertex_right (p.withParam t) p.tip
  have hbound := toVertex_le_tip_add (p.withParam t) p.tip
  rw [withParam_tip, wordDist_self, withParam_param p h0 h1] at hbound
  push_cast at hbound
  show pointDist (p.withParam t) (vertex A p.tip) ≤ 1 - t
  rw [hvia] at hle
  linarith

end Point

/-! ## Retracting a point to an endpoint of its edge -/

/-- The path that runs from `p` to the base vertex of its edge, at unit speed,
and stays there. -/
noncomputable def retractBase (A : Alphabet G) (p : Point A) : ℝ → Point A :=
  fun r => if r ≤ 0 then p else
    if p.param ≤ r then vertex A p.base else p.withParam (p.param - r)

/-- The path that runs from `p` to the far vertex of its edge, at unit speed,
and stays there. -/
noncomputable def retractTip (A : Alphabet G) (p : Point A) : ℝ → Point A :=
  fun r => if r ≤ 0 then p else
    if 1 - p.param ≤ r then vertex A p.tip else p.withParam (p.param + r)

theorem retractBase_zero (A : Alphabet G) (p : Point A) :
    retractBase A p 0 = p := by
  show (if (0 : ℝ) ≤ 0 then p else
    if p.param ≤ 0 then vertex A p.base else p.withParam (p.param - 0)) = p
  rw [if_pos (le_refl (0 : ℝ))]

/-- The base retraction ends at distance zero from the base vertex.  It cannot
end **at** it: when `p.param = 0` the path has length zero, so it is still `p`,
which is at distance zero from the vertex without being equal to it. -/
theorem dist_retractBase_end (A : Alphabet G) (p : Point A) :
    dist (retractBase A p p.param) (vertex A p.base) = 0 := by
  by_cases h : p.param ≤ 0
  · have hp : p.param = 0 := le_antisymm h p.param_nonneg
    have hval : retractBase A p p.param = p := by
      show (if p.param ≤ 0 then p else
        if p.param ≤ p.param then vertex A p.base
          else p.withParam (p.param - p.param)) = p
      rw [if_pos h]
    have hle : dist p (vertex A p.base) ≤ p.param := by
      have h1 := Point.dist_withParam_base_le p p.param_nonneg p.param_le_one
      rw [Point.withParam_self] at h1
      exact h1
    have hge : (0 : ℝ) ≤ dist p (vertex A p.base) := dist_nonneg
    rw [hp] at hle
    rw [hval]
    linarith
  · have hval : retractBase A p p.param = vertex A p.base := by
      show (if p.param ≤ 0 then p else
        if p.param ≤ p.param then vertex A p.base
          else p.withParam (p.param - p.param)) = vertex A p.base
      rw [if_neg h, if_pos (le_refl p.param)]
    rw [hval, dist_self]

theorem retractTip_zero (A : Alphabet G) (p : Point A) :
    retractTip A p 0 = p := by
  show (if (0 : ℝ) ≤ 0 then p else
    if 1 - p.param ≤ 0 then vertex A p.tip else p.withParam (p.param + 0)) = p
  rw [if_pos (le_refl (0 : ℝ))]

/-- The far retraction ends at distance zero from the far vertex. -/
theorem dist_retractTip_end (A : Alphabet G) (p : Point A) :
    dist (retractTip A p (1 - p.param)) (vertex A p.tip) = 0 := by
  by_cases h : 1 - p.param ≤ 0
  · have hval : retractTip A p (1 - p.param) = p := by
      show (if 1 - p.param ≤ 0 then p else
        if 1 - p.param ≤ 1 - p.param then vertex A p.tip
          else p.withParam (p.param + (1 - p.param))) = p
      rw [if_pos h]
    have hle : dist p (vertex A p.tip) ≤ 1 - p.param := by
      have h1 := Point.dist_withParam_tip_le p p.param_nonneg p.param_le_one
      rw [Point.withParam_self] at h1
      exact h1
    have hge : (0 : ℝ) ≤ dist p (vertex A p.tip) := dist_nonneg
    rw [hval]
    linarith
  · have hval : retractTip A p (1 - p.param) = vertex A p.tip := by
      show (if 1 - p.param ≤ 0 then p else
        if 1 - p.param ≤ 1 - p.param then vertex A p.tip
          else p.withParam (p.param + (1 - p.param))) = vertex A p.tip
      rw [if_neg h, if_pos (le_refl (1 - p.param))]
    rw [hval, dist_self]

/-! ### Evaluating the retractions -/

theorem retractBase_of_nonpos (A : Alphabet G) (p : Point A) {r : ℝ}
    (h : r ≤ 0) : retractBase A p r = p := by
  show (if r ≤ 0 then p else
    if p.param ≤ r then vertex A p.base else p.withParam (p.param - r)) = p
  rw [if_pos h]

theorem retractBase_of_far (A : Alphabet G) (p : Point A) {r : ℝ}
    (h0 : ¬ r ≤ 0) (h1 : p.param ≤ r) :
    retractBase A p r = vertex A p.base := by
  show (if r ≤ 0 then p else
    if p.param ≤ r then vertex A p.base else p.withParam (p.param - r))
    = vertex A p.base
  rw [if_neg h0, if_pos h1]

theorem retractBase_of_mem (A : Alphabet G) (p : Point A) {r : ℝ}
    (h0 : ¬ r ≤ 0) (h1 : ¬ p.param ≤ r) :
    retractBase A p r = p.withParam (p.param - r) := by
  show (if r ≤ 0 then p else
    if p.param ≤ r then vertex A p.base else p.withParam (p.param - r))
    = p.withParam (p.param - r)
  rw [if_neg h0, if_neg h1]

theorem retractTip_of_nonpos (A : Alphabet G) (p : Point A) {r : ℝ}
    (h : r ≤ 0) : retractTip A p r = p := by
  show (if r ≤ 0 then p else
    if 1 - p.param ≤ r then vertex A p.tip else p.withParam (p.param + r)) = p
  rw [if_pos h]

theorem retractTip_of_far (A : Alphabet G) (p : Point A) {r : ℝ}
    (h0 : ¬ r ≤ 0) (h1 : 1 - p.param ≤ r) :
    retractTip A p r = vertex A p.tip := by
  show (if r ≤ 0 then p else
    if 1 - p.param ≤ r then vertex A p.tip else p.withParam (p.param + r))
    = vertex A p.tip
  rw [if_neg h0, if_pos h1]

theorem retractTip_of_mem (A : Alphabet G) (p : Point A) {r : ℝ}
    (h0 : ¬ r ≤ 0) (h1 : ¬ 1 - p.param ≤ r) :
    retractTip A p r = p.withParam (p.param + r) := by
  show (if r ≤ 0 then p else
    if 1 - p.param ≤ r then vertex A p.tip else p.withParam (p.param + r))
    = p.withParam (p.param + r)
  rw [if_neg h0, if_neg h1]

/-! ### The retractions are `1`-Lipschitz -/

/-- The base retraction is `1`-Lipschitz on `[0, p.param]`. -/
theorem retractBase_lipschitz (A : Alphabet G) (p : Point A) :
    ∀ s ∈ Set.Icc (0 : ℝ) p.param, ∀ t ∈ Set.Icc (0 : ℝ) p.param, s ≤ t →
      dist (retractBase A p s) (retractBase A p t) ≤ t - s := by
  intro s hs t ht hst
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  have hp0 := p.param_nonneg
  have hp1 := p.param_le_one
  have hself : p.withParam p.param = p := Point.withParam_self p
  by_cases hsz : s ≤ 0
  · rw [retractBase_of_nonpos A p hsz]
    by_cases htz : t ≤ 0
    · rw [retractBase_of_nonpos A p htz, dist_self]
      linarith
    · by_cases hte : p.param ≤ t
      · rw [retractBase_of_far A p htz hte]
        have h := Point.dist_withParam_base_le p hp0 hp1
        rw [hself] at h
        linarith
      · rw [retractBase_of_mem A p htz hte]
        have h := Point.dist_withParam_le p hp0 hp1
          (by linarith : (0 : ℝ) ≤ p.param - t) (by linarith)
        rw [hself, abs_of_nonneg
          (by linarith : (0 : ℝ) ≤ p.param - (p.param - t))] at h
        linarith
  · have htz : ¬ t ≤ 0 := fun h => hsz (le_trans hst h)
    by_cases hse : p.param ≤ s
    · have hte : p.param ≤ t := le_trans hse hst
      rw [retractBase_of_far A p hsz hse, retractBase_of_far A p htz hte,
        dist_self]
      linarith
    · rw [retractBase_of_mem A p hsz hse]
      by_cases hte : p.param ≤ t
      · rw [retractBase_of_far A p htz hte]
        have h := Point.dist_withParam_base_le p
          (by linarith : (0 : ℝ) ≤ p.param - s) (by linarith)
        linarith
      · rw [retractBase_of_mem A p htz hte]
        have h := Point.dist_withParam_le p
          (by linarith : (0 : ℝ) ≤ p.param - s) (by linarith)
          (by linarith : (0 : ℝ) ≤ p.param - t) (by linarith)
        rw [abs_of_nonneg
          (by linarith : (0 : ℝ) ≤ p.param - s - (p.param - t))] at h
        linarith

/-- The far retraction is `1`-Lipschitz on `[0, 1 - p.param]`. -/
theorem retractTip_lipschitz (A : Alphabet G) (p : Point A) :
    ∀ s ∈ Set.Icc (0 : ℝ) (1 - p.param), ∀ t ∈ Set.Icc (0 : ℝ) (1 - p.param),
      s ≤ t → dist (retractTip A p s) (retractTip A p t) ≤ t - s := by
  intro s hs t ht hst
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  have hp0 := p.param_nonneg
  have hp1 := p.param_le_one
  have hself : p.withParam p.param = p := Point.withParam_self p
  by_cases hsz : s ≤ 0
  · rw [retractTip_of_nonpos A p hsz]
    by_cases htz : t ≤ 0
    · rw [retractTip_of_nonpos A p htz, dist_self]
      linarith
    · by_cases hte : 1 - p.param ≤ t
      · rw [retractTip_of_far A p htz hte]
        have h := Point.dist_withParam_tip_le p hp0 hp1
        rw [hself] at h
        linarith
      · rw [retractTip_of_mem A p htz hte]
        have h := Point.dist_withParam_le p hp0 hp1
          (by linarith : (0 : ℝ) ≤ p.param + t) (by linarith)
        rw [hself, abs_of_nonpos
          (by linarith : p.param - (p.param + t) ≤ 0)] at h
        linarith
  · have htz : ¬ t ≤ 0 := fun h => hsz (le_trans hst h)
    by_cases hse : 1 - p.param ≤ s
    · have hte : 1 - p.param ≤ t := le_trans hse hst
      rw [retractTip_of_far A p hsz hse, retractTip_of_far A p htz hte,
        dist_self]
      linarith
    · rw [retractTip_of_mem A p hsz hse]
      by_cases hte : 1 - p.param ≤ t
      · rw [retractTip_of_far A p htz hte]
        have h := Point.dist_withParam_tip_le p
          (by linarith : (0 : ℝ) ≤ p.param + s) (by linarith)
        linarith
      · rw [retractTip_of_mem A p htz hte]
        have h := Point.dist_withParam_le p
          (by linarith : (0 : ℝ) ≤ p.param + s) (by linarith)
          (by linarith : (0 : ℝ) ≤ p.param + t) (by linarith)
        rw [abs_of_nonpos
          (by linarith : p.param + s - (p.param + t) ≤ 0)] at h
        linarith

/-! ## Reversing a retraction -/

/-- Running a `1`-Lipschitz path backwards leaves it `1`-Lipschitz. -/
theorem lipschitz_reverse {A : Alphabet G} {γ : ℝ → Point A} {L : ℝ}
    (h : ∀ s ∈ Set.Icc (0 : ℝ) L, ∀ t ∈ Set.Icc (0 : ℝ) L, s ≤ t →
      dist (γ s) (γ t) ≤ t - s) :
    ∀ s ∈ Set.Icc (0 : ℝ) L, ∀ t ∈ Set.Icc (0 : ℝ) L, s ≤ t →
      dist (γ (L - s)) (γ (L - t)) ≤ t - s := by
  intro s hs t ht hst
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  have h' := h (L - t) ⟨by linarith, by linarith⟩ (L - s)
    ⟨by linarith, by linarith⟩ (by linarith)
  rw [dist_comm]
  linarith

/-! ## The three-piece path -/

/-- **The assembly.**  A retraction of `p` onto a vertex `v`, a geodesic between
vertices, and a retraction of `q` onto a vertex `w` run backwards, concatenated,
give a geodesic from `p` to `q` — provided the three lengths add up to the
distance.  Only `1`-Lipschitz bounds on the pieces are used, since
`isGeodesicSegment_of_lipschitz` supplies the rest. -/
theorem exists_geodesic_of_split (A : Alphabet G) (p q : Point A) (v w : G)
    (α ζ : ℝ) (hα : 0 ≤ α) (hζ : 0 ≤ ζ)
    (γ₁ : ℝ → Point A) (hγ₁0 : γ₁ 0 = p)
    (hγ₁α : dist (γ₁ α) (vertex A v) = 0)
    (hγ₁lip : ∀ s ∈ Set.Icc (0 : ℝ) α, ∀ t ∈ Set.Icc (0 : ℝ) α, s ≤ t →
      dist (γ₁ s) (γ₁ t) ≤ t - s)
    (γ₃ : ℝ → Point A) (hγ₃0 : dist (γ₃ 0) (vertex A w) = 0) (hγ₃ζ : γ₃ ζ = q)
    (hγ₃lip : ∀ s ∈ Set.Icc (0 : ℝ) ζ, ∀ t ∈ Set.Icc (0 : ℝ) ζ, s ≤ t →
      dist (γ₃ s) (γ₃ t) ≤ t - s)
    (hd : dist p q = α + (wordDist A.carrier v w : ℝ) + ζ) :
    ∃ f : ℝ → Point A, IsGeodesicSegment f 0 (dist p q) ∧ f 0 = p ∧
      f (dist p q) = q := by
  classical
  obtain ⟨γ₂, hγ₂geo, hγ₂0, hγ₂β⟩ :=
    exists_vertexGeodesic A (wordDist A.carrier v w) v w rfl
  have hβ : (0 : ℝ) ≤ (wordDist A.carrier v w : ℝ) := by positivity
  have hd0 : (0 : ℝ) ≤ dist p q := dist_nonneg
  have hnot1 : ¬ dist p q ≤ α := by rw [hd]; linarith
  have hnot2 : ¬ dist p q ≤ α + (wordDist A.carrier v w : ℝ) := by
    rw [hd]; linarith
  have hsub : dist p q - α - (wordDist A.carrier v w : ℝ) = ζ := by rw [hd]; ring
  -- Distances from a point of each piece to the two junction vertices.
  have hj1 : ∀ r : ℝ, 0 ≤ r → r ≤ α → dist (γ₁ r) (vertex A v) ≤ α - r := by
    intro r hr0 hr1
    have h := hγ₁lip r ⟨hr0, hr1⟩ α ⟨hα, le_refl α⟩ hr1
    have h2 := dist_triangle (γ₁ r) (γ₁ α) (vertex A v)
    rw [hγ₁α] at h2
    linarith
  have hj2 : ∀ r : ℝ, 0 ≤ r → r ≤ (wordDist A.carrier v w : ℝ) →
      dist (vertex A v) (γ₂ r) ≤ r := by
    intro r hr0 hr1
    have h := hγ₂geo 0 ⟨le_refl 0, hβ⟩ r ⟨hr0, hr1⟩
    rw [hγ₂0] at h
    rw [h, abs_of_nonpos (by linarith)]
    linarith
  have hj3 : ∀ r : ℝ, 0 ≤ r → r ≤ (wordDist A.carrier v w : ℝ) →
      dist (γ₂ r) (vertex A w) ≤ (wordDist A.carrier v w : ℝ) - r := by
    intro r hr0 hr1
    have h := hγ₂geo r ⟨hr0, hr1⟩ (wordDist A.carrier v w : ℝ) ⟨hβ, le_refl _⟩
    rw [hγ₂β] at h
    rw [h, abs_of_nonpos (by linarith)]
    linarith
  have hj4 : ∀ r : ℝ, 0 ≤ r → r ≤ ζ → dist (vertex A w) (γ₃ r) ≤ r := by
    intro r hr0 hr1
    have h := hγ₃lip 0 ⟨le_refl 0, hζ⟩ r ⟨hr0, hr1⟩ hr0
    have h2 := dist_triangle (vertex A w) (γ₃ 0) (γ₃ r)
    rw [dist_comm (vertex A w) (γ₃ 0), hγ₃0] at h2
    linarith
  have hvw : dist (vertex A v) (vertex A w) ≤ (wordDist A.carrier v w : ℝ) := by
    have h := hγ₂geo 0 ⟨le_refl 0, hβ⟩ (wordDist A.carrier v w : ℝ)
      ⟨hβ, le_refl _⟩
    rw [hγ₂0, hγ₂β, abs_of_nonpos (by linarith)] at h
    linarith
  refine ⟨fun r => if r ≤ α then γ₁ r else
    if r ≤ α + (wordDist A.carrier v w : ℝ) then γ₂ (r - α)
      else γ₃ (r - α - (wordDist A.carrier v w : ℝ)), ?_, ?_, ?_⟩
  · refine isGeodesicSegment_of_lipschitz hd0 ?_ ?_
    · rw [if_pos hα, if_neg hnot1, if_neg hnot2, hγ₁0, hsub, hγ₃ζ]
    · intro s hs t ht hst
      obtain ⟨hs0, hs1⟩ := hs
      obtain ⟨ht0, ht1⟩ := ht
      rw [hd] at hs1 ht1
      by_cases hsA : s ≤ α
      · by_cases htA : t ≤ α
        · rw [if_pos hsA, if_pos htA]
          exact hγ₁lip s ⟨hs0, hsA⟩ t ⟨ht0, htA⟩ hst
        · by_cases htB : t ≤ α + (wordDist A.carrier v w : ℝ)
          · rw [if_pos hsA, if_neg htA, if_pos htB]
            have h1 := hj1 s hs0 hsA
            have h2 := hj2 (t - α) (by linarith) (by linarith)
            have h3 := dist_triangle (γ₁ s) (vertex A v) (γ₂ (t - α))
            linarith
          · rw [if_pos hsA, if_neg htA, if_neg htB]
            have h1 := hj1 s hs0 hsA
            have h3 := hj4 (t - α - (wordDist A.carrier v w : ℝ))
              (by linarith) (by linarith)
            have h4 := dist_triangle (γ₁ s) (vertex A v)
              (γ₃ (t - α - (wordDist A.carrier v w : ℝ)))
            have h5 := dist_triangle (vertex A v) (vertex A w)
              (γ₃ (t - α - (wordDist A.carrier v w : ℝ)))
            linarith
      · have htA : ¬ t ≤ α := fun h => hsA (le_trans hst h)
        by_cases hsB : s ≤ α + (wordDist A.carrier v w : ℝ)
        · by_cases htB : t ≤ α + (wordDist A.carrier v w : ℝ)
          · rw [if_neg hsA, if_pos hsB, if_neg htA, if_pos htB]
            have h := hγ₂geo (s - α) ⟨by linarith, by linarith⟩ (t - α)
              ⟨by linarith, by linarith⟩
            rw [h, abs_of_nonpos (by linarith)]
            linarith
          · rw [if_neg hsA, if_pos hsB, if_neg htA, if_neg htB]
            have h1 := hj3 (s - α) (by linarith) (by linarith)
            have h2 := hj4 (t - α - (wordDist A.carrier v w : ℝ))
              (by linarith) (by linarith)
            have h3 := dist_triangle (γ₂ (s - α)) (vertex A w)
              (γ₃ (t - α - (wordDist A.carrier v w : ℝ)))
            linarith
        · have htB : ¬ t ≤ α + (wordDist A.carrier v w : ℝ) :=
            fun h => hsB (le_trans hst h)
          rw [if_neg hsA, if_neg hsB, if_neg htA, if_neg htB]
          exact hγ₃lip (s - α - (wordDist A.carrier v w : ℝ))
            ⟨by linarith, by linarith⟩
            (t - α - (wordDist A.carrier v w : ℝ))
            ⟨by linarith, by linarith⟩ (by linarith)
  · rw [if_pos hα, hγ₁0]
  · rw [if_neg hnot1, if_neg hnot2, hsub, hγ₃ζ]

/-! ## The realisation is geodesic -/

/-- **`IsGeodesicRealisation`, discharged.**  The case analysis is
`pointDist_cases` — the distance is realised along a shared edge or through the
vertices — and then `viaVertex_cases` and `toVertex_cases`, which name the two
endpoints the four ways go through.  In each leaf the length identity that
`exists_geodesic_of_split` asks for is exactly what those `cases` lemmas
say. -/
theorem isGeodesicRealisation (A : Alphabet G) : IsGeodesicRealisation A := by
  classical
  intro p q
  have hp0 := p.param_nonneg
  have hp1 := p.param_le_one
  have hq0 := q.param_nonneg
  have hq1 := q.param_le_one
  rcases Point.pointDist_cases p q with hvia | ⟨⟨hb, hl⟩, hedge⟩
  · rcases Point.viaVertex_cases p q with hq | hq
    · rcases Point.toVertex_cases p q.base with hpc | hpc
      · exact exists_geodesic_of_split A p q p.base q.base p.param q.param
          hp0 hq0
          (retractBase A p) (retractBase_zero A p) (dist_retractBase_end A p)
          (retractBase_lipschitz A p)
          (fun u => retractBase A q (q.param - u))
          (by simp only [sub_zero]; exact dist_retractBase_end A q)
          (by simp only [sub_self]; exact retractBase_zero A q)
          (lipschitz_reverse (retractBase_lipschitz A q))
          (by show Point.pointDist p q = _; rw [hvia, hq, hpc])
      · exact exists_geodesic_of_split A p q p.tip q.base (1 - p.param) q.param
          (by linarith) hq0
          (retractTip A p) (retractTip_zero A p) (dist_retractTip_end A p)
          (retractTip_lipschitz A p)
          (fun u => retractBase A q (q.param - u))
          (by simp only [sub_zero]; exact dist_retractBase_end A q)
          (by simp only [sub_self]; exact retractBase_zero A q)
          (lipschitz_reverse (retractBase_lipschitz A q))
          (by show Point.pointDist p q = _; rw [hvia, hq, hpc])
    · rcases Point.toVertex_cases p q.tip with hpc | hpc
      · exact exists_geodesic_of_split A p q p.base q.tip p.param (1 - q.param)
          hp0 (by linarith)
          (retractBase A p) (retractBase_zero A p) (dist_retractBase_end A p)
          (retractBase_lipschitz A p)
          (fun u => retractTip A q (1 - q.param - u))
          (by simp only [sub_zero]; exact dist_retractTip_end A q)
          (by simp only [sub_self]; exact retractTip_zero A q)
          (lipschitz_reverse (retractTip_lipschitz A q))
          (by show Point.pointDist p q = _; rw [hvia, hq, hpc])
      · exact exists_geodesic_of_split A p q p.tip q.tip (1 - p.param)
          (1 - q.param) (by linarith) (by linarith)
          (retractTip A p) (retractTip_zero A p) (dist_retractTip_end A p)
          (retractTip_lipschitz A p)
          (fun u => retractTip A q (1 - q.param - u))
          (by simp only [sub_zero]; exact dist_retractTip_end A q)
          (by simp only [sub_self]; exact retractTip_zero A q)
          (lipschitz_reverse (retractTip_lipschitz A q))
          (by show Point.pointDist p q = _; rw [hvia, hq, hpc])
  · -- `p` and `q` share an edge and the distance is realised along it.
    have hq_eq : p.withParam q.param = q :=
      Point.ext' hb hl (Point.withParam_param p hq0 hq1)
    have hdist : dist p q = |p.param - q.param| := hedge
    rcases le_total p.param q.param with hle | hle
    · have hd : dist p q = q.param - p.param := by
        rw [hdist, abs_of_nonpos (by linarith)]
        ring
      refine ⟨fun r => p.withParam (p.param + r), ?_, ?_, ?_⟩
      · refine isGeodesicSegment_of_lipschitz dist_nonneg ?_ ?_
        · rw [add_zero, Point.withParam_self, hd]
          have hpar : p.param + (q.param - p.param) = q.param := by ring
          rw [hpar, hq_eq, hd]
        · intro s hs t ht hst
          rw [hd] at hs ht
          exact le_trans (Point.dist_withParam_le p (by linarith [hs.1])
            (by linarith [hs.2]) (by linarith [ht.1]) (by linarith [ht.2]))
            (le_of_eq (by rw [abs_of_nonpos (by linarith)]; ring))
      · rw [add_zero, Point.withParam_self]
      · rw [hd]
        have hpar : p.param + (q.param - p.param) = q.param := by ring
        rw [hpar, hq_eq]
    · have hd : dist p q = p.param - q.param := by
        rw [hdist, abs_of_nonneg (by linarith)]
      refine ⟨fun r => p.withParam (p.param - r), ?_, ?_, ?_⟩
      · refine isGeodesicSegment_of_lipschitz dist_nonneg ?_ ?_
        · rw [sub_zero, Point.withParam_self, hd]
          have hpar : p.param - (p.param - q.param) = q.param := by ring
          rw [hpar, hq_eq, hd]
        · intro s hs t ht hst
          rw [hd] at hs ht
          exact le_trans (Point.dist_withParam_le p (by linarith [hs.2])
            (by linarith [hs.1]) (by linarith [ht.2]) (by linarith [ht.1]))
            (le_of_eq (by rw [abs_of_nonneg (by linarith)]; ring))
      · rw [sub_zero, Point.withParam_self]
      · rw [hd]
        have hpar : p.param - (p.param - q.param) = q.param := by ring
        rw [hpar, hq_eq]

end CayleyGeodesicModel
end GGT
end GroupApproximation
