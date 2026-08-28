import GroupApproximation.Algebra.HyperbolicSlimTriangles

/-!
# Slim triangles imply Gromov's four-point condition

`Algebra/HyperbolicSlimTriangles.lean` records `SlimImpliesFourPoint` as an open
`Prop`-valued definition: the direction of the classical equivalence (Bridson
and Haefliger, *Metric Spaces of Non-Positive Curvature*, III.H.1.17; Ghys and
de la Harpe) that turns the slim-triangles picture into the inequality
`Algebra/HyperbolicGroup.lean` takes as the definition of hyperbolicity.

This module proves it, with no citation and no analytic input:

* `exists_isBetween_twiceGromovProduct_le` --- the geometric half of the
  comparison between Gromov products and distances to sides;
* `isFourPointHyperbolic_of_isSlimTriangles` --- `δ`-slim triangles give the
  four-point condition at `3δ + 1`;
* `slimImpliesFourPoint` --- the recorded statement, discharged;
* `isHyperbolicGroup_of_isSlimTriangles` --- the form a consumer wants: slim
  triangles over a *finite* symmetric alphabet make the group hyperbolic.

## The one lemma that carries the geometry

`twiceGromovProduct_le_of_isBetween` is the elementary half: every point
between `b` and `c` is at least `(b·c)_a` from `a`, by three triangle
inequalities.  The other half --- that *some* point between `b` and `c` is
within a bounded distance of `(b·c)_a` from `a` --- is where slimness enters,
and it is `exists_isBetween_twiceGromovProduct_le`.

The proof is a discrete transition argument rather than the continuity argument
of the metric-space textbooks.  Call `i` *good* when some point at distance `i`
from `a` on a geodesic to `b` is `δ`-close to the side `[b,c]`; that is
`NearFarSide`.  The distance `d(a,b)` is good, because `b` lies on `[b,c]`, so
there is a least good `i`.

* If the least good `i` is `0`, the vertex `a` itself is within `δ` of `[b,c]`,
  and `(b·c)_a ≥ 0` finishes it.
* Otherwise `i - 1` is not good, so slimness at *any* point `pk` at distance
  `i - 1` --- one exists by `exists_isBetween`, since the Cayley graph is
  geodesic --- must put `pk` within `δ` of the *other* side `[a,c]`, at some
  `q₁`.  Going from `b` to `c` through `pk` and `q₁` then costs at most
  `d(b,pk) + δ + d(q₁,c)`, which is `d(a,b) + d(a,c) - 2(i-1) + 2δ`, so

  ```
      2 (i - 1) ≤ d(a,b) + d(a,c) - d(b,c) + 2δ ,
  ```

  and the point of `[b,c]` that `i` was good for is within `δ` of distance `i`
  from `a`.

The two points at distances `i` and `i - 1` are chosen independently and are
never compared with each other, which is what removes the need for a
continuity, or discrete-continuity, step: no geodesic has to be traversed one
letter at a time.

## The constant

`δ`-slim gives `3δ + 1`.  The `+1` is the price of the discrete transition
(the least good `i` beats `i - 1` by one), and the `3` is one `δ` for each of
the three approximations: `pk` to `q₁`, `p` to its point of `[b,c]`, and the
point of `[b,c]` to the side of the second triangle.  No attempt is made to
sharpen it; every consumer quantifies the constant existentially.

## The converse, and the equivalence

`FourPointImpliesSlim` is proved too, at `4δ`, and it needs no transition
argument: two applications of the four-point condition at the vertex `x` bound
the Gromov product `(p·q)_x` of a point `p` of `[x,y]` and the point `q` of
`[x,z]` at the same distance from `x`, and `d(p,q)` is what is left over.  The
case `d(x,p) > (y·z)_x` is the same argument run from `y`, since
`(y·z)_x + (x·z)_y = d(x,y)`.

So `exists_isSlimTriangles_iff_exists_isFourPointHyperbolic`: over a fixed
symmetric generating set the two conditions are equivalent, with constants
`3δ + 1` and `4δ`.  Both statements that
`Algebra/HyperbolicSlimTriangles.lean` records as open are now theorems.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GroupApproximation
namespace Hyperbolic

open WordMetric

universe u

variable {G : Type u} [Group G]

/-! ## Betweenness is symmetric in its endpoints -/

/-- Betweenness does not see the order of the two endpoints. -/
theorem IsBetween.symm {S : Set G} (hS : IsSymmetricGeneratingSet S) {b p c : G}
    (h : IsBetween S b p c) : IsBetween S c p b := by
  have hbp := wordDist_comm hS b p
  have hpc := wordDist_comm hS p c
  have hbc := wordDist_comm hS b c
  have h' : wordDist S b p + wordDist S p c = wordDist S b c := h
  show wordDist S c p + wordDist S p b = wordDist S c b
  omega

/-! ## The transition predicate -/

/-- **`i` is good**: some point at distance `i` from `a` on a geodesic to `b`
is within `δ` of the side `[b,c]`.  The least good `i` is where the proof of
`exists_isBetween_twiceGromovProduct_le` cuts. -/
def NearFarSide (S : Set G) (δ : ℕ) (a b c : G) (i : ℕ) : Prop :=
  ∃ p : G, IsBetween S a p b ∧ wordDist S a p = i ∧
    ∃ q : G, IsBetween S c q b ∧ wordDist S p q ≤ δ

/-- The full distance is good: the endpoint `b` lies on `[b,c]`. -/
theorem nearFarSide_wordDist {S : Set G} (δ : ℕ) (a b c : G) :
    NearFarSide S δ a b c (wordDist S a b) := by
  refine ⟨b, isBetween_right a b, rfl, b, isBetween_right c b, ?_⟩
  rw [wordDist_self]
  exact Nat.zero_le δ

/-! ## The geometric half of the comparison -/

/-- **Slim triangles put a point of `[b,c]` close to the Gromov product.**

`twiceGromovProduct_le_of_isBetween` says every point between `b` and `c` is at
least `(b·c)_a` from `a`.  This is the converse direction, and the only place
slimness is used: some point between `b` and `c` is within `2δ + 1` of
`(b·c)_a` from `a`, stated doubled so that no division appears. -/
theorem exists_isBetween_twiceGromovProduct_le {S : Set G} {δ : ℕ}
    (hS : IsSymmetricGeneratingSet S) (hslim : IsSlimTriangles S δ) (a b c : G) :
    ∃ q : G, IsBetween S b q c ∧
      2 * (wordDist S a q : ℤ) ≤ twiceGromovProduct S a b c + (4 * δ + 2) := by
  classical
  have hex : ∃ i, NearFarSide S δ a b c i :=
    ⟨wordDist S a b, nearFarSide_wordDist δ a b c⟩
  have hspec : ∃ p : G, IsBetween S a p b ∧ wordDist S a p = Nat.find hex ∧
      ∃ q : G, IsBetween S c q b ∧ wordDist S p q ≤ δ := Nat.find_spec hex
  obtain ⟨p, hpab, hpdist, q₀, hq₀cb, hq₀close⟩ := hspec
  have hle : Nat.find hex ≤ wordDist S a b :=
    Nat.find_min' hex (nearFarSide_wordDist δ a b c)
  have htri_aq₀ : wordDist S a q₀ ≤ wordDist S a p + wordDist S p q₀ :=
    wordDist_triangle hS a p q₀
  refine ⟨q₀, IsBetween.symm hS hq₀cb, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hzero | hpos
  · -- The vertex `a` is itself within `δ` of the side `[b,c]`.
    have hp0 : wordDist S a p = 0 := hpdist.trans hzero
    have htri_bc : wordDist S b c ≤ wordDist S b a + wordDist S a c :=
      wordDist_triangle hS b a c
    have hcomm : wordDist S b a = wordDist S a b := wordDist_comm hS b a
    simp only [twiceGromovProduct]
    omega
  · -- The predecessor of the least good distance is not good, so slimness
    -- pushes a point at that distance onto the other side.
    have hkle : Nat.find hex - 1 ≤ wordDist S a b := by omega
    obtain ⟨pk, hpkab, hpkdist⟩ := exists_isBetween hS a b hkle
    have hnotk : ¬ NearFarSide S δ a b c (Nat.find hex - 1) :=
      Nat.find_min hex (by omega)
    have hP : ∃ q : G, IsBetween S a q c ∧ wordDist S pk q ≤ δ := by
      rcases hslim a b c pk hpkab with h | h
      · exact h
      · exact absurd
          (show NearFarSide S δ a b c (Nat.find hex - 1) from ⟨pk, hpkab, hpkdist, h⟩)
          hnotk
    obtain ⟨q₁, hq₁ac, hq₁close⟩ := hP
    have hpab' : wordDist S a p + wordDist S p b = wordDist S a b := hpab
    have hpkab' : wordDist S a pk + wordDist S pk b = wordDist S a b := hpkab
    have hq₁ac' : wordDist S a q₁ + wordDist S q₁ c = wordDist S a c := hq₁ac
    have htri_bc : wordDist S b c ≤ wordDist S b q₁ + wordDist S q₁ c :=
      wordDist_triangle hS b q₁ c
    have htri_bq₁ : wordDist S b q₁ ≤ wordDist S b pk + wordDist S pk q₁ :=
      wordDist_triangle hS b pk q₁
    have htri_apk : wordDist S a pk ≤ wordDist S a q₁ + wordDist S q₁ pk :=
      wordDist_triangle hS a q₁ pk
    have hcomm₁ : wordDist S b pk = wordDist S pk b := wordDist_comm hS b pk
    have hcomm₂ : wordDist S q₁ pk = wordDist S pk q₁ := wordDist_comm hS q₁ pk
    simp only [twiceGromovProduct]
    omega

/-! ## The four-point condition -/

/-- **Slim triangles imply Gromov's four-point condition**, at `3δ + 1`.

Both halves of the comparison are used once.  A point `q` between `x` and `y`
is chosen within `2δ + 1` of `(x·y)_w` from `w`; slimness of the triangle
`x y z` moves it within `δ` of a point `r` on one of the other two sides; and
`twiceGromovProduct_le_of_isBetween` reads the resulting bound on `d(w,r)` as a
bound on the Gromov product carried by that side. -/
theorem isFourPointHyperbolic_of_isSlimTriangles {S : Set G} {δ : ℕ}
    (hS : IsSymmetricGeneratingSet S) (hslim : IsSlimTriangles S δ) :
    IsFourPointHyperbolic S (3 * δ + 1) := by
  rw [isFourPointHyperbolic_iff_gromovProduct hS]
  intro w x y z
  obtain ⟨q, hqxy, hqle⟩ := exists_isBetween_twiceGromovProduct_le hS hslim w x y
  rcases hslim x y z q hqxy with ⟨r, hr, hd⟩ | ⟨r, hr, hd⟩
  · -- `r` lies on `[x,z]`, so the product `(x·z)_w` is the one that is beaten.
    have hA : twiceGromovProduct S w x z ≤ 2 * (wordDist S w r : ℤ) :=
      twiceGromovProduct_le_of_isBetween hS w hr
    have htri : wordDist S w r ≤ wordDist S w q + wordDist S q r :=
      wordDist_triangle hS w q r
    have hmin : min (twiceGromovProduct S w x z) (twiceGromovProduct S w y z)
        ≤ twiceGromovProduct S w x z := min_le_left _ _
    simp only [twiceGromovProduct] at hA hqle hmin ⊢
    omega
  · -- `r` lies on `[z,y]`, and `(z·y)_w` is `(y·z)_w` by symmetry of the metric.
    have hA : twiceGromovProduct S w z y ≤ 2 * (wordDist S w r : ℤ) :=
      twiceGromovProduct_le_of_isBetween hS w hr
    have htri : wordDist S w r ≤ wordDist S w q + wordDist S q r :=
      wordDist_triangle hS w q r
    have hmin : min (twiceGromovProduct S w x z) (twiceGromovProduct S w y z)
        ≤ twiceGromovProduct S w y z := min_le_right _ _
    have hcomm : wordDist S z y = wordDist S y z := wordDist_comm hS z y
    simp only [twiceGromovProduct] at hA hqle hmin ⊢
    omega

/-- **`SlimImpliesFourPoint`, discharged.**  The statement
`Algebra/HyperbolicSlimTriangles.lean` records as open. -/
theorem slimImpliesFourPoint : SlimImpliesFourPoint := by
  intro H inst S δ hS hslim
  exact ⟨3 * δ + 1, isFourPointHyperbolic_of_isSlimTriangles hS hslim⟩

/-- **Slim triangles over a finite alphabet make the group hyperbolic.**  This
is the form a consumer wants: a combinatorial argument that produces slim
triangles --- small cancellation, for instance --- now lands in
`Hyperbolic.IsHyperbolicGroup` without any further geometry. -/
theorem isHyperbolicGroup_of_isSlimTriangles {S : Finset G} {δ : ℕ}
    (hS : IsSymmetricGeneratingSet (S : Set G))
    (hslim : IsSlimTriangles (S : Set G) δ) : IsHyperbolicGroup G :=
  ⟨S, hS, 3 * δ + 1, isFourPointHyperbolic_of_isSlimTriangles hS hslim⟩

/-! ## The converse

`FourPointImpliesSlim` is the other statement
`Algebra/HyperbolicSlimTriangles.lean` records as open.  It is the easier
direction here, and it is pure arithmetic: the Gromov product of the two
candidate points is bounded below by two applications of the four-point
condition, and the distance between them is what is left over. -/

/-- **A point on `[x,y]` no further from `x` than the Gromov product `(y·z)_x`
is `4δ` from the point of `[x,z]` at the same distance.**

Two applications of the four-point condition at `x`: the first, with the
auxiliary point `y`, bounds `(p·z)_x` below by `min ((p·y)_x, (y·z)_x) - δ`,
which is `d(x,p) - δ` because `p` lies on `[x,y]` and `d(x,p) ≤ (y·z)_x`; the
second, with the auxiliary point `z`, bounds `(p·q)_x` below by
`d(x,p) - 2δ` because `q` lies on `[x,z]` at distance `d(x,p)`.  Then
`d(p,q) = d(x,p) + d(x,q) - 2 (p·q)_x ≤ 4δ`.  Everything is doubled, so no
division appears. -/
theorem exists_isBetween_close_of_fourPoint {S : Set G} {δ : ℕ}
    (hS : IsSymmetricGeneratingSet S) (hδ : IsFourPointHyperbolic S δ)
    (x y z p : G) (hp : IsBetween S x p y)
    (ht : 2 * (wordDist S x p : ℤ) ≤ twiceGromovProduct S x y z) :
    ∃ q : G, IsBetween S x q z ∧ wordDist S p q ≤ 4 * δ := by
  have hgp := (isFourPointHyperbolic_iff_gromovProduct hS δ).mp hδ
  have hp' : wordDist S x p + wordDist S p y = wordDist S x y := hp
  have hcomm_yz : wordDist S z y = wordDist S y z := wordDist_comm hS z y
  have hxy_tri : wordDist S x y ≤ wordDist S x z + wordDist S z y :=
    wordDist_triangle hS x z y
  simp only [twiceGromovProduct] at ht
  have hle : wordDist S x p ≤ wordDist S x z := by omega
  obtain ⟨q, hq, hqd⟩ := exists_isBetween hS x z hle
  have hq' : wordDist S x q + wordDist S q z = wordDist S x z := hq
  have h1 := hgp x p z y
  have h2 := hgp x p q z
  have hA : 2 * (wordDist S x p : ℤ)
      ≤ min (twiceGromovProduct S x p y) (twiceGromovProduct S x z y) := by
    refine le_min ?_ ?_
    · simp only [twiceGromovProduct]
      omega
    · simp only [twiceGromovProduct]
      omega
  have hB : 2 * (wordDist S x p : ℤ) - 2 * δ ≤ twiceGromovProduct S x p z := by omega
  have hC : 2 * (wordDist S x p : ℤ) - 2 * δ
      ≤ min (twiceGromovProduct S x p z) (twiceGromovProduct S x q z) := by
    refine le_min hB ?_
    simp only [twiceGromovProduct]
    omega
  have hD : 2 * (wordDist S x p : ℤ) - 4 * δ ≤ twiceGromovProduct S x p q := by omega
  refine ⟨q, hq, ?_⟩
  simp only [twiceGromovProduct] at hD
  omega

/-- **Gromov's four-point condition makes triangles slim**, at `4δ`.  The point
`p` is compared with the side `[x,z]` when it is on the `x` half of `[x,y]`,
and with `[z,y]` otherwise; the two halves are separated by the Gromov product
`(y·z)_x`, and `(x·z)_y` is what is left of `d(x,y)`. -/
theorem isSlimTriangles_of_isFourPointHyperbolic {S : Set G} {δ : ℕ}
    (hS : IsSymmetricGeneratingSet S) (hδ : IsFourPointHyperbolic S δ) :
    IsSlimTriangles S (4 * δ) := by
  intro x y z p hp
  by_cases hcase : 2 * (wordDist S x p : ℤ) ≤ twiceGromovProduct S x y z
  · obtain ⟨q, hq, hd⟩ := exists_isBetween_close_of_fourPoint hS hδ x y z p hp hcase
    exact Or.inl ⟨q, hq, hd⟩
  · have hp' : wordDist S x p + wordDist S p y = wordDist S x y := hp
    have hcomm_yp : wordDist S y p = wordDist S p y := wordDist_comm hS y p
    have hcomm_yx : wordDist S y x = wordDist S x y := wordDist_comm hS y x
    have hcase' : 2 * (wordDist S y p : ℤ) ≤ twiceGromovProduct S y x z := by
      simp only [twiceGromovProduct] at hcase ⊢
      omega
    obtain ⟨q, hq, hd⟩ :=
      exists_isBetween_close_of_fourPoint hS hδ y x z p (IsBetween.symm hS hp) hcase'
    exact Or.inr ⟨q, IsBetween.symm hS hq, hd⟩

/-- **`FourPointImpliesSlim`, discharged.** -/
theorem fourPointImpliesSlim : FourPointImpliesSlim := by
  intro H inst S δ hS hδ
  exact ⟨4 * δ, isSlimTriangles_of_isFourPointHyperbolic hS hδ⟩

/-- **The two conditions are equivalent**, in the repository's discrete
setting: over a fixed symmetric generating set, having slim triangles at some
constant and satisfying the four-point condition at some constant are the same
statement.  Both directions are proved here, with the constants `3δ + 1` and
`4δ`. -/
theorem exists_isSlimTriangles_iff_exists_isFourPointHyperbolic {S : Set G}
    (hS : IsSymmetricGeneratingSet S) :
    (∃ δ : ℕ, IsSlimTriangles S δ) ↔ (∃ δ : ℕ, IsFourPointHyperbolic S δ) := by
  constructor
  · rintro ⟨δ, h⟩
    exact ⟨3 * δ + 1, isFourPointHyperbolic_of_isSlimTriangles hS h⟩
  · rintro ⟨δ, h⟩
    exact ⟨4 * δ, isSlimTriangles_of_isFourPointHyperbolic hS h⟩

end Hyperbolic
end GroupApproximation
