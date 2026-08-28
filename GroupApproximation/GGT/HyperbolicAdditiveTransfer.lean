import GroupApproximation.Sofic.HullSuitabilityGeometry

/-!
# Transferring hyperbolic geometry along a map of bounded additive distortion

Every predicate of `Sofic/HullSuitabilityGeometry.lean` --- `IsHyperbolicSpace`,
`IsLoxodromic`, `Independent`, `ActsNonElementarily`, `IsAcylindrical` --- is a
statement about distances up to bounded error, so each of them transfers along a
map `f : X → Y` that changes every distance by at most an additive constant `C`,
with a constant this module computes explicitly.  Nothing here is asymptotic and
nothing here is a citation.

## Why the additive case, and only the additive case

The four-point condition is *not* preserved by a general `(λ, c)`-quasi-isometry
for elementary reasons: dividing every distance by `λ` divides the Gromov
products by `λ` too, and an inequality `min (x·y)_w (y·z)_w - δ ≤ (x·z)_w` does
not survive an unknown rescaling of `δ`.  What repairs it is the Morse lemma ---
quasi-geodesics in a geodesic hyperbolic space stay uniformly close to
geodesics --- and that is a genuine theorem, not an estimate.  It is *not*
proved here.  `MorseLemmaStatement` writes it down as a named `Prop`, so that
anything depending on quasi-isometry invariance can be stated conditionally on
it with the dependence visible in the statement, and
`QuasiIsometryHyperbolicityStatement` writes down the consequence consumers
actually want.

For `λ = 1` --- an additive distortion --- no Morse lemma is needed, because the
Gromov product itself moves by at most `3C/2`:

```
    |(f x · f y)_{f w} - (x · y)_w| ≤ 3C/2,
```

which is `abs_gromovProduct_sub_le`: three applications of the distortion bound,
halved.  Everything else in the module is that inequality plus bookkeeping.

## What is proved

* `isHyperbolicSpace_of_additiveDistortion` --- a `δ`-hyperbolic target gives a
  `(δ + 3C)`-hyperbolic source.  No equivariance, no density: the distortion
  bound alone.
* `isLoxodromic_map`, `isLoxodromic_of_map` --- loxodromy transfers in both
  directions along an equivariant `f`, with the translation rate `l` unchanged
  and the additive constant paying `B ↦ B + C`.
* `independent_map`, `independent_of_map`, `actsNonElementarily_map` --- the
  same for independence, and hence for non-elementarity, at `C₀ ↦ C₀ + 3C/2`.
* `isAcylindrical_of_additiveDistortion` --- acylindricity pulls back along an
  equivariant `f` with no density hypothesis, at `(R, ε) ↦ (R + C, ε + C)`.
* `isAcylindrical_of_additiveDistortion_of_dense` --- and pushes forward when
  the image is `C`-dense and the target action is isometric, at
  `(R, ε) ↦ (R + 3C, ε + 3C)`.  The cardinality bound `N` is unchanged in both
  directions, because each proof exhibits one `ε`-stabiliser as a *subset* of
  another.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry

universe u v w

/-! ## The three hypotheses -/

/-- **Equivariance** of a map between two spaces carrying an action of the same
group. -/
def IsEquivariant (G : Type u) [Group G] {X : Type v} {Y : Type w}
    [MulAction G X] [MulAction G Y] (f : X → Y) : Prop :=
  ∀ (a : G) (u : X), f (a • u) = a • f u

section Defs

variable {X : Type v} {Y : Type w} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- **Additive distortion**: `f` changes every distance by at most `C`.  This is
a `(1, C)`-quasi-isometric embedding, and the multiplicative constant being one
is exactly what makes the four-point condition transfer without the Morse
lemma. -/
def HasAdditiveDistortion (C : ℝ) (f : X → Y) : Prop :=
  ∀ a b : X, |dist (f a) (f b) - dist a b| ≤ C

/-- **`C`-dense image**: every point of the target lies within `C` of the image.
With `HasAdditiveDistortion C f` this makes `f` a `(1, C)`-quasi-isometry rather
than only an embedding. -/
def HasDenseImage (C : ℝ) (f : X → Y) : Prop :=
  ∀ u : Y, ∃ a : X, dist (f a) u ≤ C

end Defs

/-! ## The Gromov product moves by at most `3C/2` -/

section Product

variable {X : Type v} {Y : Type w} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- **The key estimate.**  A map of additive distortion `C` moves every Gromov
product by at most `3C/2`: the product is built from three distances, and the
factor `1/2` halves their combined error. -/
theorem abs_gromovProduct_sub_le {C : ℝ} {f : X → Y}
    (hf : HasAdditiveDistortion C f) (x y w : X) :
    |gromovProduct (f x) (f y) (f w) - gromovProduct x y w| ≤ 3 * C / 2 := by
  obtain ⟨h1, h2⟩ := abs_le.mp (hf x w)
  obtain ⟨h3, h4⟩ := abs_le.mp (hf y w)
  obtain ⟨h5, h6⟩ := abs_le.mp (hf x y)
  simp only [gromovProduct]
  rw [abs_le]
  constructor <;> linarith

/-- **Hyperbolicity pulls back along a map of additive distortion**, with the
constant `δ + 3C`.  Neither density nor equivariance is used. -/
theorem isHyperbolicSpace_of_additiveDistortion {C δ : ℝ} {f : X → Y}
    (hf : HasAdditiveDistortion C f) (hY : IsHyperbolicSpace δ Y) :
    IsHyperbolicSpace (δ + 3 * C) X := by
  intro w x y z
  have hxy1 := (abs_le.mp (abs_gromovProduct_sub_le hf x y w)).1
  have hyz1 := (abs_le.mp (abs_gromovProduct_sub_le hf y z w)).1
  have hxz2 := (abs_le.mp (abs_gromovProduct_sub_le hf x z w)).2
  have hY' := hY (f w) (f x) (f y) (f z)
  have hml := min_le_left (gromovProduct x y w) (gromovProduct y z w)
  have hmr := min_le_right (gromovProduct x y w) (gromovProduct y z w)
  have hlow : min (gromovProduct x y w) (gromovProduct y z w) - 3 * C / 2
      ≤ min (gromovProduct (f x) (f y) (f w))
          (gromovProduct (f y) (f z) (f w)) :=
    le_min (by linarith) (by linarith)
  linarith

end Product

/-! ## Transfer along an equivariant map -/

section Equivariant

variable {G : Type u} [Group G] {X : Type v} {Y : Type w}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] [MulAction G X] [MulAction G Y]

/-- **Loxodromy pushes forward.**  The translation rate is unchanged; only the
additive constant grows, by `C`. -/
theorem isLoxodromic_map {C : ℝ} (hC : 0 ≤ C) {f : X → Y}
    (hf : HasAdditiveDistortion C f) (hequiv : IsEquivariant G f)
    {g : G} {x : X} (hg : IsLoxodromic g x) : IsLoxodromic g (f x) := by
  obtain ⟨l, hl, B, hB, hlin⟩ := hg
  refine ⟨l, hl, B + C, by linarith, ?_⟩
  intro n
  have h1 := hlin n
  have h2 := hf x ((g ^ n) • x)
  rw [hequiv (g ^ n) x] at h2
  have h2a := (abs_le.mp h2).1
  linarith

/-- **Loxodromy pulls back**, at the same cost. -/
theorem isLoxodromic_of_map {C : ℝ} (hC : 0 ≤ C) {f : X → Y}
    (hf : HasAdditiveDistortion C f) (hequiv : IsEquivariant G f)
    {g : G} {x : X} (hg : IsLoxodromic g (f x)) : IsLoxodromic g x := by
  obtain ⟨l, hl, B, hB, hlin⟩ := hg
  refine ⟨l, hl, B + C, by linarith, ?_⟩
  intro n
  have h1 := hlin n
  have h2 := hf x ((g ^ n) • x)
  rw [hequiv (g ^ n) x] at h2
  have h2b := (abs_le.mp h2).2
  linarith

/-- **Independence pushes forward**, at the cost `C₀ ↦ C₀ + 3C/2`. -/
theorem independent_map {C : ℝ} {f : X → Y} (hf : HasAdditiveDistortion C f)
    (hequiv : IsEquivariant G f) {g₁ g₂ : G} {x : X}
    (hind : Independent g₁ g₂ x) : Independent g₁ g₂ (f x) := by
  obtain ⟨C₀, hC₀⟩ := hind
  refine ⟨C₀ + 3 * C / 2, ?_⟩
  intro n m
  have h := abs_gromovProduct_sub_le hf ((g₁ ^ n) • x) ((g₂ ^ m) • x) x
  rw [hequiv (g₁ ^ n) x, hequiv (g₂ ^ m) x] at h
  have hb := (abs_le.mp h).2
  have h0 := hC₀ n m
  linarith

/-- **Independence pulls back**, at the same cost. -/
theorem independent_of_map {C : ℝ} {f : X → Y} (hf : HasAdditiveDistortion C f)
    (hequiv : IsEquivariant G f) {g₁ g₂ : G} {x : X}
    (hind : Independent g₁ g₂ (f x)) : Independent g₁ g₂ x := by
  obtain ⟨C₀, hC₀⟩ := hind
  refine ⟨C₀ + 3 * C / 2, ?_⟩
  intro n m
  have h := abs_gromovProduct_sub_le hf ((g₁ ^ n) • x) ((g₂ ^ m) • x) x
  rw [hequiv (g₁ ^ n) x, hequiv (g₂ ^ m) x] at h
  have ha := (abs_le.mp h).1
  have h0 := hC₀ n m
  linarith

/-- **Non-elementarity pushes forward.**  Both clauses are the two transfers
above, applied to the same pair of elements. -/
theorem actsNonElementarily_map {C : ℝ} (hC : 0 ≤ C) {f : X → Y}
    (hf : HasAdditiveDistortion C f) (hequiv : IsEquivariant G f)
    {S : Subgroup G} {x : X} (h : ActsNonElementarily S x) :
    ActsNonElementarily S (f x) := by
  obtain ⟨g₁, hg₁, g₂, hg₂, hlox₁, hlox₂, hind⟩ := h
  exact ⟨g₁, hg₁, g₂, hg₂, isLoxodromic_map hC hf hequiv hlox₁,
    isLoxodromic_map hC hf hequiv hlox₂, independent_map hf hequiv hind⟩

/-- **Acylindricity pulls back** along an equivariant map of additive
distortion.  No density hypothesis is needed: the `ε`-stabiliser of a pair in
the source is contained in the `(ε + C)`-stabiliser of its image, and a subset
of a finite set of bounded size has bounded size. -/
theorem isAcylindrical_of_additiveDistortion {C : ℝ} (hC : 0 ≤ C) {f : X → Y}
    (hf : HasAdditiveDistortion C f) (hequiv : IsEquivariant G f)
    (hY : IsAcylindrical G Y) : IsAcylindrical G X := by
  intro ε hε
  obtain ⟨R, N, hRN⟩ := hY (ε + C) (by linarith)
  refine ⟨R + C, N, ?_⟩
  intro x y hxy
  have hfxy : R ≤ dist (f x) (f y) := by
    have h1 := (abs_le.mp (hf x y)).1
    linarith
  obtain ⟨hfin, hcard⟩ := hRN (f x) (f y) hfxy
  have hsub : {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε} ⊆
      {g : G | dist (f x) (g • f x) ≤ ε + C ∧
        dist (f y) (g • f y) ≤ ε + C} := by
    rintro g ⟨h1, h2⟩
    have e1 := hf x (g • x)
    have e2 := hf y (g • y)
    rw [hequiv g x] at e1
    rw [hequiv g y] at e2
    have e1b := (abs_le.mp e1).2
    have e2b := (abs_le.mp e2).2
    exact ⟨by linarith, by linarith⟩
  exact ⟨hfin.subset hsub, le_trans (Set.ncard_le_ncard hsub hfin) hcard⟩

/-- **Acylindricity pushes forward** along an equivariant map of additive
distortion with `C`-dense image, provided the target action is by isometries:
the `ε`-stabiliser of a pair in the target is contained in the
`(ε + 3C)`-stabiliser of a pair of `C`-approximants in the source. -/
theorem isAcylindrical_of_additiveDistortion_of_dense {C : ℝ} (hC : 0 ≤ C)
    {f : X → Y} (hf : HasAdditiveDistortion C f) (hdense : HasDenseImage C f)
    (hequiv : IsEquivariant G f) (hisoY : IsIsometricAction G Y)
    (hX : IsAcylindrical G X) : IsAcylindrical G Y := by
  intro ε hε
  obtain ⟨R, N, hRN⟩ := hX (ε + 3 * C) (by linarith)
  refine ⟨R + 3 * C, N, ?_⟩
  intro u v huv
  obtain ⟨a, ha⟩ := hdense u
  obtain ⟨b, hb⟩ := hdense v
  have hau : dist u (f a) ≤ C := by rwa [dist_comm]
  have hbv : dist v (f b) ≤ C := by rwa [dist_comm]
  have hab : R ≤ dist a b := by
    have h1 := (abs_le.mp (hf a b)).2
    have h3 := dist_triangle4 u (f a) (f b) v
    have h4 : dist (f b) v = dist v (f b) := dist_comm _ _
    linarith
  obtain ⟨hfin, hcard⟩ := hRN a b hab
  have hsub : {g : G | dist u (g • u) ≤ ε ∧ dist v (g • v) ≤ ε} ⊆
      {g : G | dist a (g • a) ≤ ε + 3 * C ∧
        dist b (g • b) ≤ ε + 3 * C} := by
    rintro g ⟨h1, h2⟩
    have e1 := hf a (g • a)
    have e2 := hf b (g • b)
    rw [hequiv g a] at e1
    rw [hequiv g b] at e2
    have e1a := (abs_le.mp e1).1
    have e2a := (abs_le.mp e2).1
    have t1 := dist_triangle4 (f a) u (g • u) (g • f a)
    have t2 := dist_triangle4 (f b) v (g • v) (g • f b)
    have s1 : dist (g • u) (g • f a) = dist u (f a) := hisoY g u (f a)
    have s2 : dist (g • v) (g • f b) = dist v (f b) := hisoY g v (f b)
    exact ⟨by linarith, by linarith⟩
  exact ⟨hfin.subset hsub, le_trans (Set.ncard_le_ncard hsub hfin) hcard⟩

end Equivariant

/-! ## What the quasi-isometric case would need -/

/-- **The Morse lemma (stability of quasi-geodesics)**, written down as the
statement that is missing and is *not proved here*.

In a geodesic `δ`-hyperbolic space, a `(λ, c)`-quasi-geodesic segment stays
within distance `M(δ, λ, c)` --- depending on the three constants only, not on
the space and not on the segment --- of any geodesic with the same endpoints.
The order of the quantifiers is the whole content: `M` is chosen before the
space.

This is Bridson--Haefliger, *Metric Spaces of Non-Positive Curvature*, Part
III.H, Theorem 1.7, and Ghys--de la Harpe, *Sur les groupes hyperboliques
d'apres Mikhael Gromov*, Chapitre 3.  Anything in this repository needing
quasi-isometry invariance of hyperbolicity should carry this as an explicit
hypothesis rather than assert it. -/
def MorseLemmaStatement : Prop :=
  ∀ δ lam c : ℝ, 0 ≤ δ → 0 < lam → 0 ≤ c → ∃ M : ℝ, 0 ≤ M ∧
    ∀ (Z : Type) [_inst : PseudoMetricSpace Z], IsGeodesicSpace Z →
      IsHyperbolicSpace δ Z → ∀ (p q : ℝ → Z) (a b : ℝ), a ≤ b →
        (∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
            |s - t| / lam - c ≤ dist (p s) (p t) ∧
              dist (p s) (p t) ≤ lam * |s - t| + c) →
          IsGeodesicSegment q a b → q a = p a → q b = p b →
            ∀ s ∈ Set.Icc a b, ∃ t ∈ Set.Icc a b, dist (p s) (q t) ≤ M

/-- **Quasi-isometry invariance of hyperbolicity**, written down as the
statement `MorseLemmaStatement` exists in order to supply, and *not proved
here*: a `(λ, c)`-quasi-isometry between geodesic spaces carries the four-point
condition to the four-point condition, at a constant depending only on
`δ`, `λ` and `c`.

Stated separately from the Morse lemma because it is what consumers want, and
because the implication between the two is itself a theorem rather than an
unfolding.  `isHyperbolicSpace_of_additiveDistortion` is the special case
`λ = 1`, which this module proves outright. -/
def QuasiIsometryHyperbolicityStatement : Prop :=
  ∀ δ lam c : ℝ, 0 ≤ δ → 0 < lam → 0 ≤ c → ∃ δ' : ℝ, 0 ≤ δ' ∧
    ∀ (Z W : Type) [_instZ : PseudoMetricSpace Z]
      [_instW : PseudoMetricSpace W],
      IsGeodesicSpace Z → IsGeodesicSpace W → IsHyperbolicSpace δ W →
        ∀ f : Z → W,
          (∀ a b : Z, dist a b / lam - c ≤ dist (f a) (f b) ∧
              dist (f a) (f b) ≤ lam * dist a b + c) →
            (∀ u : W, ∃ a : Z, dist (f a) u ≤ c) → IsHyperbolicSpace δ' Z

end GGT
end GroupApproximation
