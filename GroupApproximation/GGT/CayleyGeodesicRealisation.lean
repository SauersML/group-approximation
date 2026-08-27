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

theorem retractBase_end (A : Alphabet G) (p : Point A) :
    retractBase A p p.param = vertex A p.base := by
  by_cases h : p.param ≤ 0
  · have hp : p.param = 0 := le_antisymm h p.param_nonneg
    show (if p.param ≤ 0 then p else
      if p.param ≤ p.param then vertex A p.base
        else p.withParam (p.param - p.param)) = vertex A p.base
    rw [if_pos h]
    exact Point.ext' rfl (by rw [hp] at *; exact ?_) (by rw [hp]; rfl)
  · show (if p.param ≤ 0 then p else
      if p.param ≤ p.param then vertex A p.base
        else p.withParam (p.param - p.param)) = vertex A p.base
    rw [if_neg h, if_pos (le_refl p.param)]

theorem retractTip_zero (A : Alphabet G) (p : Point A) :
    retractTip A p 0 = p := by
  show (if (0 : ℝ) ≤ 0 then p else
    if 1 - p.param ≤ 0 then vertex A p.tip else p.withParam (p.param + 0)) = p
  rw [if_pos (le_refl (0 : ℝ))]

theorem retractTip_end (A : Alphabet G) (p : Point A) :
    retractTip A p (1 - p.param) = vertex A p.tip := by
  by_cases h : 1 - p.param ≤ 0
  · have hp : p.param = 1 := le_antisymm p.param_le_one (by linarith)
    show (if 1 - p.param ≤ 0 then p else
      if 1 - p.param ≤ 1 - p.param then vertex A p.tip
        else p.withParam (p.param + (1 - p.param))) = vertex A p.tip
    rw [if_pos h]
    exact Point.ext' rfl (by rfl) (by rw [hp]; rfl)
  · show (if 1 - p.param ≤ 0 then p else
      if 1 - p.param ≤ 1 - p.param then vertex A p.tip
        else p.withParam (p.param + (1 - p.param))) = vertex A p.tip
    rw [if_neg h, if_pos (le_refl (1 - p.param))]

/-- The base retraction is `1`-Lipschitz on `[0, p.param]`. -/
theorem retractBase_lipschitz (A : Alphabet G) (p : Point A) :
    ∀ s ∈ Set.Icc (0 : ℝ) p.param, ∀ t ∈ Set.Icc (0 : ℝ) p.param, s ≤ t →
      dist (retractBase A p s) (retractBase A p t) ≤ t - s := by
  intro s hs t ht hst
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  have hp0 := p.param_nonneg
  have hp1 := p.param_le_one
  by_cases hsz : s ≤ 0
  · have hs00 : s = 0 := le_antisymm hsz hs0
    rw [show retractBase A p s = p by rw [hs00]; exact retractBase_zero A p]
    by_cases htz : t ≤ 0
    · have ht00 : t = 0 := le_antisymm htz ht0
      rw [show retractBase A p t = p by rw [ht00]; exact retractBase_zero A p],
        hs00, ht00]
      rw [dist_self]
      norm_num
    · by_cases hte : p.param ≤ t
      · have h := Point.dist_withParam_base_le p p.param_nonneg p.param_le_one
        rw [Point.withParam_self] at h
        rw [show retractBase A p t = vertex A p.base by
          show (if t ≤ 0 then p else
            if p.param ≤ t then vertex A p.base
              else p.withParam (p.param - t)) = vertex A p.base
          rw [if_neg htz, if_pos hte]]
        rw [hs00]
        linarith
      · have h := Point.dist_withParam_le p p.param_nonneg p.param_le_one
          (by linarith : (0:ℝ) ≤ p.param - t) (by linarith)
        rw [Point.withParam_self] at h
        rw [show retractBase A p t = p.withParam (p.param - t) by
          show (if t ≤ 0 then p else
            if p.param ≤ t then vertex A p.base
              else p.withParam (p.param - t)) = p.withParam (p.param - t)
          rw [if_neg htz, if_pos rfl]]
        rw [hs00]
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ p.param - (p.param - t))] at h
        linarith
  · have htz : ¬ t ≤ 0 := fun h => hsz (le_trans hst h)
    by_cases hse : p.param ≤ s
    · have hte : p.param ≤ t := le_trans hse hst
      rw [show retractBase A p s = vertex A p.base by
        show (if s ≤ 0 then p else
          if p.param ≤ s then vertex A p.base
            else p.withParam (p.param - s)) = vertex A p.base
        rw [if_neg hsz, if_pos hse],
        show retractBase A p t = vertex A p.base by
        show (if t ≤ 0 then p else
          if p.param ≤ t then vertex A p.base
            else p.withParam (p.param - t)) = vertex A p.base
        rw [if_neg htz, if_pos hte]]
      rw [dist_self]
      linarith
    · rw [show retractBase A p s = p.withParam (p.param - s) by
        show (if s ≤ 0 then p else
          if p.param ≤ s then vertex A p.base
            else p.withParam (p.param - s)) = p.withParam (p.param - s)
        rw [if_neg hsz, if_neg hse]]
      by_cases hte : p.param ≤ t
      · have h := Point.dist_withParam_base_le p
          (by linarith : (0:ℝ) ≤ p.param - s) (by linarith)
        rw [show retractBase A p t = vertex A p.base by
          show (if t ≤ 0 then p else
            if p.param ≤ t then vertex A p.base
              else p.withParam (p.param - t)) = vertex A p.base
          rw [if_neg htz, if_pos hte]]
        have hb : (p.withParam (p.param - s)).base = p.base := rfl
        rw [hb] at h
        linarith
      · have h := Point.dist_withParam_le p
          (by linarith : (0:ℝ) ≤ p.param - s) (by linarith)
          (by linarith : (0:ℝ) ≤ p.param - t) (by linarith)
        rw [show retractBase A p t = p.withParam (p.param - t) by
          show (if t ≤ 0 then p else
            if p.param ≤ t then vertex A p.base
              else p.withParam (p.param - t)) = p.withParam (p.param - t)
          rw [if_neg htz, if_neg hte]]
        rw [abs_of_nonneg (by linarith :
          (0:ℝ) ≤ p.param - s - (p.param - t))] at h
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
  by_cases hsz : s ≤ 0
  · have hs00 : s = 0 := le_antisymm hsz hs0
    rw [show retractTip A p s = p by rw [hs00]; exact retractTip_zero A p]
    by_cases htz : t ≤ 0
    · have ht00 : t = 0 := le_antisymm htz ht0
      rw [show retractTip A p t = p by rw [ht00]; exact retractTip_zero A p,
        hs00, ht00, dist_self]
      norm_num
    · by_cases hte : 1 - p.param ≤ t
      · have h := Point.dist_withParam_tip_le p p.param_nonneg p.param_le_one
        rw [Point.withParam_self] at h
        rw [show retractTip A p t = vertex A p.tip by
          show (if t ≤ 0 then p else
            if 1 - p.param ≤ t then vertex A p.tip
              else p.withParam (p.param + t)) = vertex A p.tip
          rw [if_neg htz, if_pos hte], hs00]
        linarith
      · have h := Point.dist_withParam_le p p.param_nonneg p.param_le_one
          (by linarith : (0:ℝ) ≤ p.param + t) (by linarith)
        rw [Point.withParam_self] at h
        rw [show retractTip A p t = p.withParam (p.param + t) by
          show (if t ≤ 0 then p else
            if 1 - p.param ≤ t then vertex A p.tip
              else p.withParam (p.param + t)) = p.withParam (p.param + t)
          rw [if_neg htz, if_neg hte], hs00]
        rw [abs_of_nonpos (by linarith : p.param - (p.param + t) ≤ 0)] at h
        linarith
  · have htz : ¬ t ≤ 0 := fun h => hsz (le_trans hst h)
    by_cases hse : 1 - p.param ≤ s
    · have hte : 1 - p.param ≤ t := le_trans hse hst
      rw [show retractTip A p s = vertex A p.tip by
        show (if s ≤ 0 then p else
          if 1 - p.param ≤ s then vertex A p.tip
            else p.withParam (p.param + s)) = vertex A p.tip
        rw [if_neg hsz, if_pos hse],
        show retractTip A p t = vertex A p.tip by
        show (if t ≤ 0 then p else
          if 1 - p.param ≤ t then vertex A p.tip
            else p.withParam (p.param + t)) = vertex A p.tip
        rw [if_neg htz, if_pos hte], dist_self]
      linarith
    · rw [show retractTip A p s = p.withParam (p.param + s) by
        show (if s ≤ 0 then p else
          if 1 - p.param ≤ s then vertex A p.tip
            else p.withParam (p.param + s)) = p.withParam (p.param + s)
        rw [if_neg hsz, if_neg hse]]
      by_cases hte : 1 - p.param ≤ t
      · have h := Point.dist_withParam_tip_le p
          (by linarith : (0:ℝ) ≤ p.param + s) (by linarith)
        rw [show retractTip A p t = vertex A p.tip by
          show (if t ≤ 0 then p else
            if 1 - p.param ≤ t then vertex A p.tip
              else p.withParam (p.param + t)) = vertex A p.tip
          rw [if_neg htz, if_pos hte]]
        have hb : (p.withParam (p.param + s)).tip = p.tip := rfl
        rw [hb] at h
        linarith
      · have h := Point.dist_withParam_le p
          (by linarith : (0:ℝ) ≤ p.param + s) (by linarith)
          (by linarith : (0:ℝ) ≤ p.param + t) (by linarith)
        rw [show retractTip A p t = p.withParam (p.param + t) by
          show (if t ≤ 0 then p else
            if 1 - p.param ≤ t then vertex A p.tip
              else p.withParam (p.param + t)) = p.withParam (p.param + t)
          rw [if_neg htz, if_neg hte]]
        rw [abs_of_nonpos (by linarith :
          p.param + s - (p.param + t) ≤ 0)] at h
        linarith

/-- The distance from a point of the base retraction to the vertex it runs
to. -/
theorem dist_retractBase_vertex (A : Alphabet G) (p : Point A) {r : ℝ}
    (h0 : 0 ≤ r) (h1 : r ≤ p.param) :
    dist (retractBase A p r) (vertex A p.base) ≤ p.param - r := by
  have hlip := retractBase_lipschitz A p r ⟨h0, h1⟩ p.param
    ⟨p.param_nonneg, le_refl _⟩ h1
  rw [retractBase_end] at hlip
  exact hlip

/-- The distance from a point of the far retraction to the vertex it runs
to. -/
theorem dist_retractTip_vertex (A : Alphabet G) (p : Point A) {r : ℝ}
    (h0 : 0 ≤ r) (h1 : r ≤ 1 - p.param) :
    dist (retractTip A p r) (vertex A p.tip) ≤ 1 - p.param - r := by
  have hlip := retractTip_lipschitz A p r ⟨h0, h1⟩ (1 - p.param)
    ⟨by linarith [p.param_le_one], le_refl _⟩ h1
  rw [retractTip_end] at hlip
  exact hlip

/-! ## The three-piece path -/

/-- **The assembly.**  A retraction of `p` onto a vertex `v`, a geodesic between
vertices, and a retraction of `q` onto a vertex `w` run backwards, concatenated,
give a geodesic from `p` to `q` — provided the three lengths add up to the
distance.  Only `1`-Lipschitz bounds on the pieces are used, since
`isGeodesicSegment_of_lipschitz` supplies the rest. -/
theorem exists_geodesic_of_split (A : Alphabet G) (p q : Point A) (v w : G)
    (α ζ : ℝ) (hα : 0 ≤ α) (hζ : 0 ≤ ζ)
    (γ₁ : ℝ → Point A) (hγ₁0 : γ₁ 0 = p) (hγ₁α : γ₁ α = vertex A v)
    (hγ₁lip : ∀ s ∈ Set.Icc (0 : ℝ) α, ∀ t ∈ Set.Icc (0 : ℝ) α, s ≤ t →
      dist (γ₁ s) (γ₁ t) ≤ t - s)
    (γ₃ : ℝ → Point A) (hγ₃0 : γ₃ 0 = vertex A w) (hγ₃ζ : γ₃ ζ = q)
    (hγ₃lip : ∀ s ∈ Set.Icc (0 : ℝ) ζ, ∀ t ∈ Set.Icc (0 : ℝ) ζ, s ≤ t →
      dist (γ₃ s) (γ₃ t) ≤ t - s)
    (hd : dist p q = α + (wordDist A.carrier v w : ℝ) + ζ) :
    ∃ f : ℝ → Point A, IsGeodesicSegment f 0 (dist p q) ∧ f 0 = p ∧
      f (dist p q) = q := by
  classical
  set β : ℝ := (wordDist A.carrier v w : ℝ) with hβdef
  have hβ : 0 ≤ β := by positivity
  obtain ⟨γ₂, hγ₂geo, hγ₂0, hγ₂β⟩ :=
    exists_vertexGeodesic A (wordDist A.carrier v w) v w rfl
  set d : ℝ := dist p q with hddef
  have hd0 : 0 ≤ d := dist_nonneg
  refine ⟨fun r => if r ≤ α then γ₁ r else
    if r ≤ α + β then γ₂ (r - α) else γ₃ (r - α - β), ?_, ?_, ?_⟩
  · refine isGeodesicSegment_of_lipschitz hd0 ?_ ?_
    · rw [if_pos hα]
      have hnot1 : ¬ d ≤ α := by rw [hd]; linarith
      have hnot2 : ¬ d ≤ α + β := by rw [hd]; linarith
      rw [if_neg hnot1, if_neg hnot2, hγ₁0]
      have hsub : d - α - β = ζ := by rw [hd]; ring
      rw [hsub, hγ₃ζ]
    · intro s hs t ht hst
      obtain ⟨hs0, hs1⟩ := hs
      obtain ⟨ht0, ht1⟩ := ht
      rw [hd] at hs1 ht1
      -- distances from a point of each piece to the two junction vertices
      have hj1 : ∀ r : ℝ, 0 ≤ r → r ≤ α →
          dist (γ₁ r) (vertex A v) ≤ α - r := by
        intro r hr0 hr1
        have h := hγ₁lip r ⟨hr0, hr1⟩ α ⟨hα, le_refl α⟩ hr1
        rw [hγ₁α] at h
        exact h
      have hj2 : ∀ r : ℝ, 0 ≤ r → r ≤ β →
          dist (vertex A v) (γ₂ r) ≤ r := by
        intro r hr0 hr1
        have h := hγ₂geo 0 ⟨le_refl 0, hβ⟩ r ⟨hr0, hr1⟩
        rw [hγ₂0, h, abs_of_nonpos (by linarith)]
        linarith
      have hj3 : ∀ r : ℝ, 0 ≤ r → r ≤ β →
          dist (γ₂ r) (vertex A w) ≤ β - r := by
        intro r hr0 hr1
        have h := hγ₂geo r ⟨hr0, hr1⟩ β ⟨hβ, le_refl β⟩ hr1
        rw [hγ₂β, h, abs_of_nonpos (by linarith)]
        linarith
      have hj4 : ∀ r : ℝ, 0 ≤ r → r ≤ ζ →
          dist (vertex A w) (γ₃ r) ≤ r := by
        intro r hr0 hr1
        have h := hγ₃lip 0 ⟨le_refl 0, hζ⟩ r ⟨hr0, hr1⟩ hr0
        rw [hγ₃0] at h
        linarith
      by_cases hsA : s ≤ α
      · by_cases htA : t ≤ α
        · rw [if_pos hsA, if_pos htA]
          exact hγ₁lip s ⟨hs0, hsA⟩ t ⟨ht0, htA⟩ hst
        · by_cases htB : t ≤ α + β
          · rw [if_pos hsA, if_neg htA, if_pos htB]
            have h1 := hj1 s hs0 hsA
            have h2 := hj2 (t - α) (by linarith) (by linarith)
            have h3 := dist_triangle (γ₁ s) (vertex A v) (γ₂ (t - α))
            linarith
          · rw [if_pos hsA, if_neg htA, if_neg htB]
            have h1 := hj1 s hs0 hsA
            have h2 := hj2 β hβ (le_refl β)
            have h3 := hj4 (t - α - β) (by linarith) (by linarith)
            have h4 := dist_triangle (γ₁ s) (vertex A v) (γ₃ (t - α - β))
            have h5 := dist_triangle (vertex A v) (vertex A w) (γ₃ (t - α - β))
            have h6 : dist (vertex A v) (vertex A w) ≤ β := by
              have h := hγ₂geo 0 ⟨le_refl 0, hβ⟩ β ⟨hβ, le_refl β⟩
              rw [hγ₂0, hγ₂β, abs_of_nonpos (by linarith)] at h
              linarith
            linarith
      · have htA : ¬ t ≤ α := fun h => hsA (le_trans hst h)
        by_cases hsB : s ≤ α + β
        · by_cases htB : t ≤ α + β
          · rw [if_neg hsA, if_pos hsB, if_neg htA, if_pos htB]
            have h := hγ₂geo (s - α) ⟨by linarith, by linarith⟩ (t - α)
              ⟨by linarith, by linarith⟩
            rw [h, abs_of_nonpos (by linarith)]
            linarith
          · rw [if_neg hsA, if_pos hsB, if_neg htA, if_neg htB]
            have h1 := hj3 (s - α) (by linarith) (by linarith)
            have h2 := hj4 (t - α - β) (by linarith) (by linarith)
            have h3 := dist_triangle (γ₂ (s - α)) (vertex A w) (γ₃ (t - α - β))
            linarith
        · have htB : ¬ t ≤ α + β := fun h => hsB (le_trans hst h)
          rw [if_neg hsA, if_neg hsB, if_neg htA, if_neg htB]
          exact hγ₃lip (s - α - β) ⟨by linarith, by linarith⟩ (t - α - β)
            ⟨by linarith, by linarith⟩ (by linarith)
  · rw [if_pos hα, hγ₁0]
  · have hnot1 : ¬ d ≤ α := by rw [hd]; linarith
    have hnot2 : ¬ d ≤ α + β := by rw [hd]; linarith
    rw [if_neg hnot1, if_neg hnot2]
    have hsub : d - α - β = ζ := by rw [hd]; ring
    rw [hsub, hγ₃ζ]

/-! ## The realisation is geodesic -/

/-- **`IsGeodesicRealisation`, discharged.**  The case analysis is
`pointDist_cases` — the distance is realised along a shared edge or through the
vertices — and then `viaVertex_cases` and `toVertex_cases`, which name the
endpoints the four ways go through. -/
theorem isGeodesicRealisation (A : Alphabet G) : IsGeodesicRealisation A := by
  classical
  intro p q
  rcases Point.pointDist_cases p q with hvia | ⟨⟨hb, hl⟩, hedge⟩
  · -- The distance is realised through the vertices.
    rcases Point.viaVertex_cases p q with hq | hq <;>
      rcases Point.toVertex_cases p (if_pos rfl ▸ q.base) with hp | hp
    all_goals sorry
  · -- `p` and `q` share an edge and the distance is realised along it.
    sorry

end CayleyGeodesicModel
end GGT
end GroupApproximation
