import GroupApproximation.Algebra.HyperbolicQuasiIsometry
import GroupApproximation.Algebra.HyperbolicSlimTriangles

/-!
# Quasi-geodesics, the Morse lemma, and what elementary transport gives

`Algebra/HyperbolicQuasiIsometry.lean` records `Hyperbolic.QuasiIsometryInvariant`
as the one open statement of this lane and names the Morse lemma as its input.
This module says precisely what that input is and how much of the transport is
elementary.

## Proved here

* `isFourPointHyperbolic_of_roughIsometry` --- **hyperbolicity is a rough-isometry
  invariant**, unconditionally, with the explicit constant `δ ↦ δ + 6C`.  A
  *rough isometry* is a quasi-isometry with multiplicative constant `1`: only the
  additive error is allowed.  Every step is a triangle inequality, and no
  geometry is needed, because an additive error passes through the four-point
  inequality by addition.
* `fourPoint_transport_of_biLipschitz` --- what the same elementary argument
  gives for a *bi-Lipschitz* change of alphabet, which is what changing the
  generating set of a group actually is
  (`Algebra/WordMetricComparison.lean`): the transported inequality carries
  `K²` in front of the maximum,

  ```
      d(w,x) + d(y,z) ≤ K² · max(...) + 2Kδ,
  ```

  and `K² > K` is not the four-point condition at any constant.  This is the
  exact shape of the obstruction: at `K = 1` the estimate *is* the four-point
  condition (`isFourPointHyperbolic_of_isometry`), and for `K > 1` no amount of
  arithmetic closes the gap.  The missing input is geometric, and it is the
  Morse lemma.

## Stated and not assumed

`IsQuasiGeodesic` and `MorseLemma` are the classical statement --- a
`(K,C)`-quasi-geodesic stays within a distance `R = R(K,C,δ)` of a geodesic with
the same endpoints, uniformly in the group --- written with the betweenness
predicate of `Algebra/HyperbolicSlimTriangles.lean`, which is how this
development says "on a geodesic" without a metric-space structure on the Cayley
graph.  `isQuasiGeodesic_of_isGeodesicWord` checks that the notion is the
intended one: the prefixes of a geodesic word are a `(1,0)`-quasi-geodesic.

Nothing in this repository assumes `MorseLemma`, and no theorem below is
conditional on it.
-/

namespace GroupApproximation
namespace Hyperbolic

open WordMetric

universe u v

/-! ## Rough isometries -/

/-- A **rough isometry**: a quasi-isometry whose multiplicative constant is `1`,
so that only an additive error is allowed. -/
def IsRoughIsometry {G : Type u} {H : Type v} [Group G] [Group H]
    (S : Set G) (T : Set H) (f : G → H) (C : ℕ) : Prop :=
  IsQuasiIsometry S T f 1 C

/-- **Hyperbolicity is a rough-isometry invariant**, with the constant
`δ ↦ δ + 6C`.

Every point of the target is within `C` of the image of a point of the source,
and the two four-point sums then differ by at most `6C` per pairing, which the
four-point inequality absorbs additively.  This is the whole of the transport
that needs no geometry --- see `fourPoint_transport_of_biLipschitz` for what
goes wrong when the multiplicative constant is allowed to exceed `1`. -/
theorem isFourPointHyperbolic_of_roughIsometry {G : Type u} {H : Type v}
    [Group G] [Group H] {S : Set G} {T : Set H} {f : G → H} {C δ : ℕ}
    (hT : IsSymmetricGeneratingSet T) (hq : IsRoughIsometry S T f C)
    (h : IsFourPointHyperbolic S δ) : IsFourPointHyperbolic T (δ + 6 * C) := by
  -- A pair of points of `T` and a pair of preimages have comparable distances.
  have key : ∀ (a b : H) (a' b' : G), wordDist T (f a') a ≤ C → wordDist T (f b') b ≤ C →
      wordDist T a b ≤ wordDist S a' b' + 3 * C ∧
        wordDist S a' b' ≤ wordDist T a b + 3 * C := by
    intro a b a' b' ha hb
    have h₁ := (hq.1 a' b').1
    have h₂ := (hq.1 a' b').2
    have c₁ : wordDist T a (f a') = wordDist T (f a') a := wordDist_comm hT _ _
    have c₂ : wordDist T b (f b') = wordDist T (f b') b := wordDist_comm hT _ _
    have t₁ : wordDist T a b ≤ wordDist T a (f a') + wordDist T (f a') b :=
      wordDist_triangle hT _ _ _
    have t₂ : wordDist T (f a') b ≤ wordDist T (f a') (f b') + wordDist T (f b') b :=
      wordDist_triangle hT _ _ _
    have t₃ : wordDist T (f a') (f b') ≤ wordDist T (f a') a + wordDist T a (f b') :=
      wordDist_triangle hT _ _ _
    have t₄ : wordDist T a (f b') ≤ wordDist T a b + wordDist T b (f b') :=
      wordDist_triangle hT _ _ _
    constructor <;> omega
  intro w x y z
  obtain ⟨w', hw⟩ := hq.2 w
  obtain ⟨x', hx⟩ := hq.2 x
  obtain ⟨y', hy⟩ := hq.2 y
  obtain ⟨z', hz⟩ := hq.2 z
  obtain ⟨hwx₁, hwx₂⟩ := key w x w' x' hw hx
  obtain ⟨hyz₁, hyz₂⟩ := key y z y' z' hy hz
  obtain ⟨hwy₁, hwy₂⟩ := key w y w' y' hw hy
  obtain ⟨hxz₁, hxz₂⟩ := key x z x' z' hx hz
  obtain ⟨hwz₁, hwz₂⟩ := key w z w' z' hw hz
  obtain ⟨hxy₁, hxy₂⟩ := key x y x' y' hx hy
  have h4 := h w' x' y' z'
  omega

/-- The packaging of `isFourPointHyperbolic_of_roughIsometry` at finite
alphabets. -/
theorem isHyperbolicGroup_of_roughIsometry {G H : Type u} [Group G] [Group H]
    {S : Finset G} {T : Finset H} {f : G → H} {C δ : ℕ}
    (hT : IsSymmetricGeneratingSet (T : Set H))
    (hq : IsRoughIsometry (S : Set G) (T : Set H) f C)
    (h : IsFourPointHyperbolic (S : Set G) δ) : IsHyperbolicGroup H :=
  ⟨T, hT, δ + 6 * C, isFourPointHyperbolic_of_roughIsometry hT hq h⟩

/-! ## What bi-Lipschitz transport gives, and why it is not enough -/

/-- **The elementary transport estimate for a bi-Lipschitz change of alphabet.**

Changing the finite generating set of a group multiplies word lengths by at most
a constant `K` in both directions (`WordMetric.exists_bilipschitz`), and pushing
the four-point condition through those two comparisons gives the displayed
inequality --- with `K²` in front of the maximum.  For `K = 1` this is the
four-point condition itself; for `K > 1` it is strictly weaker than the
four-point condition at any constant, because the defect grows with the
distances rather than staying bounded.  That gap is the reason
`Hyperbolic.IndependentOfGeneratingSet` is open here, and it is what the Morse
lemma closes. -/
theorem fourPoint_transport_of_biLipschitz {G : Type u} [Group G] {S T : Set G} {K δ : ℕ}
    (hST : ∀ x y : G, wordDist T x y ≤ K * wordDist S x y)
    (hTS : ∀ x y : G, wordDist S x y ≤ K * wordDist T x y)
    (h : IsFourPointHyperbolic S δ) :
    ∀ w x y z : G, wordDist T w x + wordDist T y z
      ≤ K * K * max (wordDist T w y + wordDist T x z) (wordDist T w z + wordDist T x y)
        + 2 * (K * δ) := by
  intro w x y z
  have hS4 := h w x y z
  have hmax : max (wordDist S w y + wordDist S x z) (wordDist S w z + wordDist S x y)
      ≤ K * max (wordDist T w y + wordDist T x z) (wordDist T w z + wordDist T x y) := by
    refine max_le ?_ ?_
    · calc wordDist S w y + wordDist S x z ≤ K * wordDist T w y + K * wordDist T x z :=
            Nat.add_le_add (hTS w y) (hTS x z)
        _ = K * (wordDist T w y + wordDist T x z) := by ring
        _ ≤ K * max (wordDist T w y + wordDist T x z) (wordDist T w z + wordDist T x y) :=
            Nat.mul_le_mul le_rfl (le_max_left _ _)
    · calc wordDist S w z + wordDist S x y ≤ K * wordDist T w z + K * wordDist T x y :=
            Nat.add_le_add (hTS w z) (hTS x y)
        _ = K * (wordDist T w z + wordDist T x y) := by ring
        _ ≤ K * max (wordDist T w y + wordDist T x z) (wordDist T w z + wordDist T x y) :=
            Nat.mul_le_mul le_rfl (le_max_right _ _)
  calc wordDist T w x + wordDist T y z ≤ K * wordDist S w x + K * wordDist S y z :=
        Nat.add_le_add (hST w x) (hST y z)
    _ = K * (wordDist S w x + wordDist S y z) := by ring
    _ ≤ K * (max (wordDist S w y + wordDist S x z) (wordDist S w z + wordDist S x y)
          + 2 * δ) := Nat.mul_le_mul le_rfl hS4
    _ ≤ K * (K * max (wordDist T w y + wordDist T x z) (wordDist T w z + wordDist T x y)
          + 2 * δ) := Nat.mul_le_mul le_rfl (by omega)
    _ = K * K * max (wordDist T w y + wordDist T x z) (wordDist T w z + wordDist T x y)
          + 2 * (K * δ) := by ring

/-- **The `K = 1` case is unconditional**: an isometric change of alphabet
preserves the four-point condition at the same constant.  This is the exact
boundary of what arithmetic reaches. -/
theorem isFourPointHyperbolic_of_isometry {G : Type u} [Group G] {S T : Set G} {δ : ℕ}
    (hST : ∀ x y : G, wordDist T x y ≤ wordDist S x y)
    (hTS : ∀ x y : G, wordDist S x y ≤ wordDist T x y)
    (h : IsFourPointHyperbolic S δ) : IsFourPointHyperbolic T δ := by
  intro w x y z
  have h4 := h w x y z
  have h₁ := hST w x
  have h₂ := hST y z
  have h₃ := hTS w y
  have h₄ := hTS x z
  have h₅ := hTS w z
  have h₆ := hTS x y
  omega

/-! ## Quasi-geodesics and the Morse lemma -/

/-- A **`(K,C)`-quasi-geodesic segment** `p 0, …, p n`: the word distance between
two of its points is comparable, with multiplicative constant `K` and additive
constant `C`, to the distance between their indices. -/
def IsQuasiGeodesic {G : Type u} [Group G] (S : Set G) (K C n : ℕ) (p : ℕ → G) : Prop :=
  ∀ i ≤ n, ∀ j ≤ n, i ≤ j →
    wordDist S (p i) (p j) ≤ K * (j - i) + C ∧ j - i ≤ K * (wordDist S (p i) (p j) + C)

/-- **The prefixes of a geodesic word are a `(1,0)`-quasi-geodesic**, so the
notion above is the intended one and its hypothesis is not vacuous. -/
theorem isQuasiGeodesic_of_isGeodesicWord {G : Type u} [Group G] {S : Set G}
    (hS : IsSymmetricGeneratingSet S) {l : List G} {g : G} (hl : IsGeodesicWord S l g) :
    IsQuasiGeodesic S 1 0 l.length (fun i => (l.take i).prod) := by
  have hstep : ∀ i j : ℕ, i ≤ j → j ≤ l.length →
      wordDist S (l.take i).prod (l.take j).prod = j - i := by
    intro i j hij hj
    have hsplit : l.take j = l.take i ++ (l.drop i).take (j - i) := by
      rw [← List.take_add]
      congr 1
      omega
    have hgeo : IsGeodesicWord S (l.take j) (l.take j).prod :=
      isGeodesicWord_take hS hl j
    rw [hsplit] at hgeo ⊢
    rw [wordDist_prod_append hS hgeo, List.length_take, List.length_drop]
    omega
  intro i hi j hj hij
  have h := hstep i j hij hj
  -- The goal reads the segment through `fun i => (l.take i).prod`, so both
  -- distances appear under a beta-redex.  `omega` compares atoms syntactically
  -- and would treat those as unrelated to `h`; beta-reduce them first.
  show wordDist S (l.take i).prod (l.take j).prod ≤ 1 * (j - i) + 0 ∧
      j - i ≤ 1 * (wordDist S (l.take i).prod (l.take j).prod + 0)
  omega

/-- **The Morse lemma** (stability of quasi-geodesics), as a statement: for each
triple of constants there is a single `R`, uniform in the group, such that in
every `δ`-hyperbolic word metric each point of a `(K,C)`-quasi-geodesic is within
`R` of a point lying between its endpoints.

This is the input `Hyperbolic.QuasiIsometryInvariant` is missing, and it is not
proved here.  Nothing in this repository assumes it. -/
def MorseLemma : Prop :=
  ∀ K C δ : ℕ, ∃ R : ℕ, ∀ (G : Type) (_ : Group G) (S : Set G),
    IsSymmetricGeneratingSet S → IsFourPointHyperbolic S δ →
      ∀ (n : ℕ) (p : ℕ → G), IsQuasiGeodesic S K C n p →
        ∀ i ≤ n, ∃ q : G, IsBetween S (p 0) q (p n) ∧ wordDist S (p i) q ≤ R

end Hyperbolic
end GroupApproximation
