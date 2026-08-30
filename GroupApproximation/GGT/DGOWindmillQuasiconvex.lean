import GroupApproximation.Sofic.HullSuitabilityGeometry

/-!
# Quasiconvex subsets of a hyperbolic geodesic space

Dahmani-Guirardel-Osin, *Hyperbolically embedded subgroups and rotating
families in groups acting on hyperbolic spaces*, Mem. Amer. Math. Soc. 245
(2017), no. 1156, §2.1 and §5.1.2.

This is the first module of the windmill campaign aimed at
`Manuscript.NonMF.TheoremCDebts.dgoTheorem53`.  After the reduction of
`GGT/DGORotatingQuotientResidual.lean` the whole of that debt is DGO's Theorem
5.3(b), the dichotomy, and DGO prove it by an induction over *windmills* --
subsets of the space that are quasiconvex with a constant independent of the
stage of the induction.  So quasiconvexity of a subset is the first vocabulary
the campaign needs, and it is not in this repository: `IsWordQuasiconvex`
(`GGT/HullSCConeOffHeavyHyperbolic.lean`) is about a subgroup of a group with a
word metric, and `IsQuasiconvexOrbitAt` (`GGT/ElementaryProjectionCriterion.lean`)
is about an orbit; neither is a statement about an arbitrary subset of an
arbitrary metric space.

## What is proved

* `exists_close_on_other_sides_of_quadrilateral` -- **geodesic quadrilaterals
  are `6δ`-thin**, from two applications of the repository's `3δ` triangle
  bound `HullGeometry.exists_close_on_other_side_of_geodesic_triangle` across a
  diagonal.  Every quasiconvexity estimate below is one call to this.
* `exists_close_of_geodesic_same_endpoints` -- **two geodesics with the same
  endpoints are `3δ`-close**, the degenerate triangle.  This is what lets the
  campaign drop DGO's Lemma 5.19 (*every* geodesic between two points of `W₂`
  coincides with one of the broken paths), and with it their shortening pairs:
  it is enough to exhibit *one* geodesic near the set and pay `3δ`.
* `isQuasiconvexSet_thicken` -- **`Q^{+r}` is `6δ`-quasiconvex whenever `Q` is
  `σ`-quasiconvex and `r ≥ σ`.**  DGO get `4δ` here through *strong*
  quasiconvexity, which their Lemma 2.x leaves to the reader; the direct
  quadrilateral argument avoids that notion entirely, at the cost of `6δ` in
  place of `4δ`.  The two outer sides of the quadrilateral have length at most
  `r` and therefore lie in `Q^{+r}` outright, which is exactly where the
  hypothesis `σ ≤ r` is spent.
* `isQuasiconvexSet_closedBall` -- **balls are `2δ`-quasiconvex**, which is what
  makes the base windmill `B(c₀, 100δ)` of DGO's induction a windmill.
* `closedBall_subset_thicken_closedBall` -- a ball thickens to a bigger ball, so
  the windmill sequence exhausts the space.

## The constants are not DGO's, and the difference is systematic

`HullGeometry.IsHyperbolicSpace δ` is Gromov's **four-point** condition, and the
triangles of such a space are `3δ`-thin, not `δ`-thin.  Every constant printed
in DGO §5.1.2 is therefore wrong for this repository by a factor that has to be
recomputed rather than transcribed.  The recomputation is carried out module by
module; here it produces `6δ` for a quadrilateral, `3δ` for two geodesics with
common endpoints, `6δ` for a neighbourhood and `2δ` for a ball.
-/

namespace GroupApproximation
namespace DGOWindmill

open GroupApproximation.HullGeometry

universe v

variable {X : Type v} [PseudoMetricSpace X]

/-! ## Neighbourhoods -/

/-- **The closed `r`-neighbourhood of a set.**  DGO write `Q^{+r}`.

Defined by hand rather than through `Metric.cthickening` because every estimate
below is a statement about a *witness* -- "this point of the geodesic is within
`6δ` of a point of `Q` at distance at most `r`" -- and an infimum over an
`ℝ≥0∞`-valued distance would have to be unpacked into exactly this shape at
every use. -/
def thicken (Q : Set X) (r : ℝ) : Set X := {x : X | ∃ q ∈ Q, dist x q ≤ r}

theorem mem_thicken_iff {Q : Set X} {r : ℝ} {x : X} :
    x ∈ thicken Q r ↔ ∃ q ∈ Q, dist x q ≤ r := Iff.rfl

theorem mem_thicken_of_dist_le {Q : Set X} {r : ℝ} {x q : X} (hq : q ∈ Q)
    (h : dist x q ≤ r) : x ∈ thicken Q r := ⟨q, hq, h⟩

theorem subset_thicken {Q : Set X} {r : ℝ} (hr : 0 ≤ r) : Q ⊆ thicken Q r :=
  fun x hx => ⟨x, hx, by rw [dist_self]; exact hr⟩

theorem thicken_mono_set {Q Q' : Set X} {r : ℝ} (h : Q ⊆ Q') :
    thicken Q r ⊆ thicken Q' r := by
  intro x hx
  obtain ⟨q, hq, hd⟩ := mem_thicken_iff.mp hx
  exact mem_thicken_of_dist_le (h hq) hd

theorem thicken_mono_radius {Q : Set X} {r r' : ℝ} (h : r ≤ r') :
    thicken Q r ⊆ thicken Q r' := by
  intro x hx
  obtain ⟨q, hq, hd⟩ := mem_thicken_iff.mp hx
  exact mem_thicken_of_dist_le hq (le_trans hd h)

theorem thicken_thicken_subset {Q : Set X} {r s : ℝ} :
    thicken (thicken Q r) s ⊆ thicken Q (r + s) := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := mem_thicken_iff.mp hx
  obtain ⟨q, hq, hpq⟩ := mem_thicken_iff.mp hp
  refine mem_thicken_of_dist_le hq ?_
  have h := dist_triangle x p q
  linarith

/-- **A distance bound survives thickening, with the thickness subtracted.**

This is the estimate the windmill's second axiom is propagated by: if every
apex of `Q` is at least `s` from `x`, then every point of `Q^{+r}` is at least
`s - r` from `x`.  DGO use it silently at `W' = W₂^{+10δ}`. -/
theorem le_dist_of_mem_thicken {Q : Set X} {r s : ℝ} {x : X}
    (h : ∀ q ∈ Q, s ≤ dist x q) {p : X} (hp : p ∈ thicken Q r) :
    s - r ≤ dist x p := by
  obtain ⟨q, hq, hpq⟩ := mem_thicken_iff.mp hp
  have h1 : s ≤ dist x q := h q hq
  -- `dist_triangle x p q` already reads `dist x q ≤ dist x p + dist p q`, and
  -- `hpq` already reads `dist p q ≤ r`; no reorientation is needed.
  have h2 := dist_triangle x p q
  linarith

theorem lt_dist_of_not_mem_thicken {Q : Set X} {r : ℝ} {x : X}
    (h : x ∉ thicken Q r) : ∀ q ∈ Q, r < dist x q := by
  intro q hq
  by_contra hle
  exact h (mem_thicken_of_dist_le hq (not_lt.mp hle))

/-! ## Quasiconvex sets -/

/-- **A `σ`-quasiconvex subset**: every geodesic between two points of `Q` stays
within `σ` of `Q`.

Quantified over parametrisations `f` in the same style as
`HullSC.IsVeryRotating`, because "every geodesic" is a statement about every
parametrisation realising the distance and there is no chosen one. -/
def IsQuasiconvexSet (Q : Set X) (σ : ℝ) : Prop :=
  ∀ x ∈ Q, ∀ y ∈ Q, ∀ f : ℝ → X, IsGeodesicSegment f 0 (dist x y) → f 0 = x →
    f (dist x y) = y → ∀ t ∈ Set.Icc (0 : ℝ) (dist x y),
      ∃ q ∈ Q, dist (f t) q ≤ σ

theorem IsQuasiconvexSet.mono {Q : Set X} {σ σ' : ℝ} (h : IsQuasiconvexSet Q σ)
    (hσ : σ ≤ σ') : IsQuasiconvexSet Q σ' := by
  intro x hx y hy f hf hf0 hf1 t ht
  obtain ⟨q, hq, hd⟩ := h x hx y hy f hf hf0 hf1 t ht
  exact ⟨q, hq, le_trans hd hσ⟩

/-! ## Thin quadrilaterals -/

/-- **Geodesic quadrilaterals are `6δ`-thin.**  A point of the side from `A` to
`D` lies within `6δ` of one of the three sides `A--B`, `B--C`, `C--D`.

Two applications of the `3δ` triangle bound across the diagonal `A--C`: the
point is `3δ` from the diagonal or from `C--D`, and a point of the diagonal is
`3δ` from `A--B` or from `B--C`.  The diagonal is supplied by the geodesic
hypothesis and is not part of the data, so no coherence between the two
applications is needed. -/
theorem exists_close_on_other_sides_of_quadrilateral {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {A B C D : X} {fAD fAB fBC fCD : ℝ → X}
    (hAD : IsGeodesicSegment fAD 0 (dist A D)) (hAD0 : fAD 0 = A)
    (hAD1 : fAD (dist A D) = D)
    (hAB : IsGeodesicSegment fAB 0 (dist A B)) (hAB0 : fAB 0 = A)
    (hAB1 : fAB (dist A B) = B)
    (hBC : IsGeodesicSegment fBC 0 (dist B C)) (hBC0 : fBC 0 = B)
    (hBC1 : fBC (dist B C) = C)
    (hCD : IsGeodesicSegment fCD 0 (dist C D)) (hCD0 : fCD 0 = C)
    (hCD1 : fCD (dist C D) = D)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (dist A D)) :
    (∃ s ∈ Set.Icc (0 : ℝ) (dist A B), dist (fAD t) (fAB s) ≤ 6 * δ) ∨
      (∃ s ∈ Set.Icc (0 : ℝ) (dist B C), dist (fAD t) (fBC s) ≤ 6 * δ) ∨
        (∃ s ∈ Set.Icc (0 : ℝ) (dist C D), dist (fAD t) (fCD s) ≤ 6 * δ) := by
  obtain ⟨fAC, hAC, hAC0, hAC1⟩ := hgeo A C
  rcases exists_close_on_other_side_of_geodesic_triangle hδ hδ0 hAD hAD0 hAD1
      hAC hAC0 hAC1 hCD hCD0 hCD1 ht with ⟨s, hs, hclose⟩ | ⟨s, hs, hclose⟩
  · rcases exists_close_on_other_side_of_geodesic_triangle hδ hδ0 hAC hAC0 hAC1
        hAB hAB0 hAB1 hBC hBC0 hBC1 hs with ⟨u, hu, hclose'⟩ | ⟨u, hu, hclose'⟩
    · refine Or.inl ⟨u, hu, ?_⟩
      have htri := dist_triangle (fAD t) (fAC s) (fAB u)
      linarith
    · refine Or.inr (Or.inl ⟨u, hu, ?_⟩)
      have htri := dist_triangle (fAD t) (fAC s) (fBC u)
      linarith
  · exact Or.inr (Or.inr ⟨s, hs, by linarith⟩)

/-! ## Two geodesics with the same endpoints -/

/-- **Two geodesics with the same endpoints `3δ`-fellow-travel.**  The
degenerate triangle `(x, y, y)`: a point of the first geodesic is `3δ` from the
second or `3δ` from `y`, and `y` is on the second.

This is the replacement for DGO's Lemma 5.19.  Their argument that *every*
geodesic between two points of `W₂` passes through the same apices exists to
turn a statement about one broken path into a statement about all geodesics;
here the same conversion costs `3δ` and no shortening pairs. -/
theorem exists_close_of_geodesic_same_endpoints {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) {x y : X} {f g : ℝ → X}
    (hf : IsGeodesicSegment f 0 (dist x y)) (hf0 : f 0 = x)
    (hf1 : f (dist x y) = y)
    (hg : IsGeodesicSegment g 0 (dist x y)) (hg0 : g 0 = x)
    (hg1 : g (dist x y) = y)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (dist x y)) :
    ∃ s ∈ Set.Icc (0 : ℝ) (dist x y), dist (f t) (g s) ≤ 3 * δ := by
  have hconst : IsGeodesicSegment (fun _ : ℝ => y) 0 (dist y y) := by
    intro s hs u hu
    have hyy : dist y y = 0 := dist_self y
    rw [hyy] at hs hu
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    have hu0 : u = 0 := le_antisymm hu.2 hu.1
    simp [hs0, hu0]
  rcases exists_close_on_other_side_of_geodesic_triangle hδ hδ0 hf hf0 hf1
      hg hg0 hg1 hconst rfl rfl ht with ⟨s, hs, hclose⟩ | ⟨s, -, hclose⟩
  · exact ⟨s, hs, hclose⟩
  · exact ⟨dist x y, ⟨dist_nonneg, le_refl _⟩, by rw [hg1]; exact hclose⟩

/-- **One geodesic per pair is enough, at a cost of `3δ`.**  If for each pair of
points of `Q` *some* geodesic stays within `σ` of `Q`, then `Q` is
`(σ + 3δ)`-quasiconvex.

This is how the campaign establishes quasiconvexity of the unfolded windmill
`W₂`: the broken path through the apices is one geodesic and is near `W₂` by
construction, and every other geodesic between the same endpoints is `3δ` from
it. -/
theorem isQuasiconvexSet_of_exists_geodesic {δ σ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) {Q : Set X}
    (h : ∀ x ∈ Q, ∀ y ∈ Q, ∃ f : ℝ → X, IsGeodesicSegment f 0 (dist x y) ∧
      f 0 = x ∧ f (dist x y) = y ∧
        ∀ t ∈ Set.Icc (0 : ℝ) (dist x y), ∃ q ∈ Q, dist (f t) q ≤ σ) :
    IsQuasiconvexSet Q (σ + 3 * δ) := by
  intro x hx y hy g hg hg0 hg1 t ht
  obtain ⟨f, hf, hf0, hf1, hnear⟩ := h x hx y hy
  obtain ⟨s, hs, hclose⟩ :=
    exists_close_of_geodesic_same_endpoints hδ hδ0 hg hg0 hg1 hf hf0 hf1 ht
  obtain ⟨q, hq, hd⟩ := hnear s hs
  refine ⟨q, hq, ?_⟩
  have htri := dist_triangle (g t) (f s) q
  linarith

/-! ## Neighbourhoods of quasiconvex sets -/

/-- **`Q^{+r}` is `6δ`-quasiconvex when `Q` is `σ`-quasiconvex and `r ≥ σ`.**

DGO reach `4δ` here through *strong* quasiconvexity, a second notion whose two
elementary lemmas their §2.1 leaves to the reader.  The quadrilateral
`x, x₀, y₀, y` gives the bound directly: a point of `[x,y]` is `6δ` from one of
the three sides, the two outer sides have length at most `r` and so lie in
`Q^{+r}`, and the middle side lies in `Q^{+σ} ⊆ Q^{+r}` by quasiconvexity of
`Q`.  That last inclusion is the only use of `σ ≤ r`, and it is what makes the
constant independent of `r`.

It is applied at `W' = W₂^{+15δ}` and at `W^{+10δ}` in the growth step, where a
constant depending on the thickness would break the induction. -/
theorem isQuasiconvexSet_thicken {δ σ r : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X) {Q : Set X}
    (hQ : IsQuasiconvexSet Q σ) (hσr : σ ≤ r) :
    IsQuasiconvexSet (thicken Q r) (6 * δ) := by
  intro x hx y hy f hf hf0 hf1 t ht
  obtain ⟨x₀, hx₀Q, hx₀⟩ := mem_thicken_iff.mp hx
  obtain ⟨y₀, hy₀Q, hy₀⟩ := mem_thicken_iff.mp hy
  obtain ⟨fAB, hAB, hAB0, hAB1⟩ := hgeo x x₀
  obtain ⟨fBC, hBC, hBC0, hBC1⟩ := hgeo x₀ y₀
  obtain ⟨fCD, hCD, hCD0, hCD1⟩ := hgeo y₀ y
  rcases exists_close_on_other_sides_of_quadrilateral hδ hδ0 hgeo hf hf0 hf1
      hAB hAB0 hAB1 hBC hBC0 hBC1 hCD hCD0 hCD1 ht with
    ⟨s, hs, hclose⟩ | ⟨s, hs, hclose⟩ | ⟨s, hs, hclose⟩
  · refine ⟨fAB s, ?_, hclose⟩
    refine mem_thicken_of_dist_le hx₀Q ?_
    have hd : dist (fAB s) (fAB (dist x x₀)) = |s - dist x x₀| :=
      hAB s hs (dist x x₀) ⟨dist_nonneg, le_refl _⟩
    rw [hAB1, abs_of_nonpos (by linarith [hs.2])] at hd
    have hs1 : (0 : ℝ) ≤ s := hs.1
    linarith
  · obtain ⟨q, hq, hqd⟩ := hQ x₀ hx₀Q y₀ hy₀Q fBC hBC hBC0 hBC1 s hs
    exact ⟨fBC s, mem_thicken_of_dist_le hq (le_trans hqd hσr), hclose⟩
  · refine ⟨fCD s, ?_, hclose⟩
    refine mem_thicken_of_dist_le hy₀Q ?_
    have hd : dist (fCD s) (fCD 0) = |s - 0| :=
      hCD s hs 0 ⟨le_refl 0, dist_nonneg⟩
    rw [hCD0, sub_zero, abs_of_nonneg hs.1] at hd
    have h2 := hs.2
    have h3 : dist y₀ y ≤ r := by rwa [dist_comm] at hy₀
    linarith

/-! ## Balls -/

/-- **Balls are `2δ`-quasiconvex.**  A point `p` of a geodesic between two
points of `B(z, R)` has `(x | y)_p = 0`, so the four-point condition forces one
of `(x | z)_p`, `(z | y)_p` below `δ`, and either bound reads
`d(z, p) ≤ R + 2δ`.  The witness in the ball is then the point of a geodesic
`[z, p]` at parameter `R`.

This is what makes the base of DGO's induction -- the ball of radius `100δ`
about a single apex -- a windmill. -/
theorem isQuasiconvexSet_closedBall {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X) (z : X) (R : ℝ) :
    IsQuasiconvexSet (Metric.closedBall z R) (2 * δ) := by
  intro x hx y hy f hf hf0 hf1 t ht
  have hxz : dist x z ≤ R := Metric.mem_closedBall.mp hx
  have hyz : dist y z ≤ R := Metric.mem_closedBall.mp hy
  have hR0 : (0 : ℝ) ≤ R := le_trans dist_nonneg hxz
  have hzero : gromovProduct x y (f t) = 0 := by
    have h := gromovProduct_eq_zero_of_mem_geodesic dist_nonneg ht hf
    rwa [hf0, hf1] at h
  have hfour := hδ (f t) x z y
  rw [hzero] at hfour
  have hmin : min (gromovProduct x z (f t)) (gromovProduct z y (f t)) ≤ δ := by
    linarith
  have hbound : dist z (f t) ≤ R + 2 * δ := by
    rcases min_le_iff.mp hmin with hleft | hright
    · unfold gromovProduct at hleft
      have hnn : (0 : ℝ) ≤ dist x (f t) := dist_nonneg
      linarith
    · unfold gromovProduct at hright
      have hnn : (0 : ℝ) ≤ dist y (f t) := dist_nonneg
      have hzy : dist z y ≤ R := by rwa [dist_comm] at hyz
      linarith
  by_cases hle : dist z (f t) ≤ R
  · refine ⟨f t, Metric.mem_closedBall.mpr ?_, ?_⟩
    · rwa [dist_comm]
    · rw [dist_self]
      linarith
  · have hlt : R < dist z (f t) := not_le.mp hle
    obtain ⟨g, hg, hg0, hg1⟩ := hgeo z (f t)
    have hmemR : R ∈ Set.Icc (0 : ℝ) (dist z (f t)) := ⟨hR0, le_of_lt hlt⟩
    refine ⟨g R, ?_, ?_⟩
    · have hd : dist (g R) (g 0) = |R - 0| :=
        hg R hmemR 0 ⟨le_refl 0, dist_nonneg⟩
      rw [hg0, sub_zero, abs_of_nonneg hR0] at hd
      exact Metric.mem_closedBall.mpr (le_of_eq hd)
    · have hd : dist (g R) (g (dist z (f t))) = |R - dist z (f t)| :=
        hg R hmemR (dist z (f t)) ⟨dist_nonneg, le_refl _⟩
      rw [hg1, abs_of_nonpos (by linarith)] at hd
      rw [dist_comm (f t) (g R)]
      linarith

/-- **A ball thickens to a bigger ball.**  In a geodesic space
`B(z, R + r) ⊆ B(z, R)^{+r}`, because a point at distance `R + r` from `z` has
the point of parameter `R` on a geodesic `[z, ·]` at distance exactly `R` from
`z` and at most `r` from it.

This is the exhaustion step: the windmill sequence of DGO's proof grows by a
fixed thickness at each stage, so its union contains every ball, hence every
apex, hence every element of the subgroup the rotations generate. -/
theorem closedBall_subset_thicken_closedBall (hgeo : IsGeodesicSpace X) (z : X)
    {R r : ℝ} (hR0 : 0 ≤ R) (hr0 : 0 ≤ r) :
    Metric.closedBall z (R + r) ⊆ thicken (Metric.closedBall z R) r := by
  intro y hy
  have hyz : dist y z ≤ R + r := Metric.mem_closedBall.mp hy
  by_cases hle : dist y z ≤ R
  · exact mem_thicken_of_dist_le (Metric.mem_closedBall.mpr hle)
      (by rw [dist_self]; exact hr0)
  · have hlt : R < dist z y := by
      rw [dist_comm]
      exact not_le.mp hle
    obtain ⟨g, hg, hg0, hg1⟩ := hgeo z y
    have hmemR : R ∈ Set.Icc (0 : ℝ) (dist z y) := ⟨hR0, le_of_lt hlt⟩
    refine mem_thicken_of_dist_le (q := g R) (Metric.mem_closedBall.mpr ?_) ?_
    · have hd : dist (g R) (g 0) = |R - 0| :=
        hg R hmemR 0 ⟨le_refl 0, dist_nonneg⟩
      rw [hg0, sub_zero, abs_of_nonneg hR0] at hd
      exact le_of_eq hd
    · have hd : dist (g R) (g (dist z y)) = |R - dist z y| :=
        hg R hmemR (dist z y) ⟨dist_nonneg, le_refl _⟩
      rw [hg1, abs_of_nonpos (by linarith)] at hd
      have hzy : dist z y ≤ R + r := by rwa [dist_comm] at hyz
      rw [dist_comm y (g R)]
      linarith

end DGOWindmill
end GroupApproximation
