import GroupApproximation.GGT.RelHypFreeProductPeripheral
import GroupApproximation.GGT.WPDHyperbolicallyEmbedded

/-!
# From the four-point condition on an alphabet to hyperbolicity of `Γ(G,A)`

Two vocabularies for the same condition live side by side in this repository and
have never been connected.

* `Algebra/HyperbolicGroup.lean` states Gromov's condition as
  `Hyperbolic.IsFourPointHyperbolic S δ`, over `ℕ`, in the subtraction-free max
  form on `WordMetric.wordDist`.  Every word-metric development produces this
  form: `isFourPointHyperbolic_intAlphabet`, `HyperbolicSlimFourPoint`,
  `HyperbolicQuasiIsometry`, `MorseLemma`.
* `Sofic/HullSuitabilityGeometry.lean` states it as
  `HullGeometry.IsHyperbolicSpace δ X`, over `ℝ`, in the min form on
  `gromovProduct`, for a `PseudoMetricSpace`.  Every *consumer* wants this form:
  `IsLoxodromic`, `Independent`, `ActsNonElementarily`, `IsAcylindrical`, and —
  the reason for this module — `RelHyp.IsRelativelyHyperbolic`, whose first
  clause is `IsHyperbolicSpace delta (Cayley X.alphabet)`.

`GGT/HyperbolicFreeGroupAH.isHyperbolicSpace_zero_cayley` crosses the gap in one
special case only: `δ = 0`, through `Hyperbolic.IsTreeLike`, where the four-point
condition *is* the ultrametric inequality and no arithmetic is needed.
`isHyperbolicSpace_cayley_of_fourPoint` crosses it in general, at the same
constant, and `isFourPointHyperbolic_of_isHyperbolicSpace` crosses back.  The
two conditions are therefore *equal*, not merely comparable: no constant is
lost in either direction, and the only lossy step in the round trip is the
`ℝ`-to-`ℕ` ceiling, which is forced by the two vocabularies disagreeing about
what a constant is rather than by any geometry.

## The arithmetic, which is a permutation and two cases

With `2·(a|b)_w = d(w,a) + d(w,b) - d(a,b)`, the min form

    min (x|y)_w (y|z)_w - δ ≤ (x|z)_w

is, after clearing the halves, the disjunction of

    d(w,y) + d(x,z) ≤ d(w,x) + d(y,z) + 2δ      (take the second term of the min)
    d(w,y) + d(x,z) ≤ d(w,z) + d(x,y) + 2δ      (take the first)

and that disjunction is exactly `IsFourPointHyperbolic` read at the quadruple
`(w, y, x, z)` — its `max` is attained at one of the two terms.  So no constant
is lost: a `δ`-four-point alphabet gives a `δ`-hyperbolic Cayley graph.
`min_gromov_le_of_fourPoint` isolates that as a statement about six reals, so the
metric bookkeeping and the arithmetic do not have to be read at once.

## What it is for

`FreeProductConedFourPointStatement` restates Farb's clause for the free product
-- the last leg of Osin, Memoirs 179, Theorem 2.34, after
`GGT/RelHypFreeProductPeripheral.lean` proved the
Dahmani--Guirardel--Osin clause -- in the `ℕ` vocabulary, at the explicit
alphabet `freeProductRelGen U H S hS` builds.  That alphabet is the *union
alphabet* of the two factors, `⋃ i, of_i '' (S i)` with `S` taken to be all of
the peripheral factor and a finite generating set of the other, so a four-point
condition proved for union alphabets in general lands on it directly, with no
quasi-isometry and hence no Morse lemma.
`freeProductConedHyperbolicStatement_of_fourPoint` is the last mile.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## 1.  The arithmetic -/

/-- **The max form implies the min form**, at six reals and with no constant
lost.  `dwy + dxz ≤ max (dwx + dyz) (dwz + dxy) + 2e` is the four-point
condition read at `(w, y, x, z)`; the `max` is attained at one of its two
arguments, and each choice discharges one branch of the `min`. -/
theorem min_gromov_le_of_fourPoint {dwx dwy dwz dxy dyz dxz e : ℝ}
    (h : dwy + dxz ≤ max (dwx + dyz) (dwz + dxy) + 2 * e) :
    min ((dwx + dwy - dxy) / 2) ((dwy + dwz - dyz) / 2) - e
      ≤ (dwx + dwz - dxz) / 2 := by
  rcases le_total (dwx + dyz) (dwz + dxy) with hle | hle
  · have hmax : max (dwx + dyz) (dwz + dxy) ≤ dwz + dxy := max_le hle le_rfl
    have hmin := min_le_left ((dwx + dwy - dxy) / 2) ((dwy + dwz - dyz) / 2)
    linarith
  · have hmax : max (dwx + dyz) (dwz + dxy) ≤ dwx + dyz := max_le le_rfl hle
    have hmin := min_le_right ((dwx + dwy - dxy) / 2) ((dwy + dwz - dyz) / 2)
    linarith

/-! ## 2.  The bridge -/

/-- **A `δ`-four-point alphabet makes `Γ(G,A)` a `δ`-hyperbolic space.**

The two statements are the same condition in two vocabularies -- `ℕ` and the max
form on `wordDist`, against `ℝ` and the min form on `gromovProduct` -- and the
constant is the same on both sides. -/
theorem isHyperbolicSpace_cayley_of_fourPoint {G : Type u} [Group G]
    (A : Alphabet G) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic A.carrier δ) :
    IsHyperbolicSpace (δ : ℝ) (Cayley A) := by
  intro w x y z
  have hS := A.symmetricGenerating
  have key := hδ (Cayley.val w) (Cayley.val y) (Cayley.val x) (Cayley.val z)
  have keyR : ((wordDist A.carrier (Cayley.val w) (Cayley.val y) : ℕ) : ℝ)
        + ((wordDist A.carrier (Cayley.val x) (Cayley.val z) : ℕ) : ℝ)
      ≤ max (((wordDist A.carrier (Cayley.val w) (Cayley.val x) : ℕ) : ℝ)
              + ((wordDist A.carrier (Cayley.val y) (Cayley.val z) : ℕ) : ℝ))
            (((wordDist A.carrier (Cayley.val w) (Cayley.val z) : ℕ) : ℝ)
              + ((wordDist A.carrier (Cayley.val y) (Cayley.val x) : ℕ) : ℝ))
        + 2 * (δ : ℝ) := by
    exact_mod_cast key
  have hcomm : wordDist A.carrier (Cayley.val y) (Cayley.val x)
      = wordDist A.carrier (Cayley.val x) (Cayley.val y) :=
    wordDist_comm hS _ _
  rw [hcomm] at keyR
  have hxw : dist x w
      = ((wordDist A.carrier (Cayley.val w) (Cayley.val x) : ℕ) : ℝ) := by
    rw [Cayley.dist_eq, wordDist_comm hS]
  have hyw : dist y w
      = ((wordDist A.carrier (Cayley.val w) (Cayley.val y) : ℕ) : ℝ) := by
    rw [Cayley.dist_eq, wordDist_comm hS]
  have hzw : dist z w
      = ((wordDist A.carrier (Cayley.val w) (Cayley.val z) : ℕ) : ℝ) := by
    rw [Cayley.dist_eq, wordDist_comm hS]
  have hxy : dist x y
      = ((wordDist A.carrier (Cayley.val x) (Cayley.val y) : ℕ) : ℝ) :=
    Cayley.dist_eq x y
  have hyz : dist y z
      = ((wordDist A.carrier (Cayley.val y) (Cayley.val z) : ℕ) : ℝ) :=
    Cayley.dist_eq y z
  have hxz : dist x z
      = ((wordDist A.carrier (Cayley.val x) (Cayley.val z) : ℕ) : ℝ) :=
    Cayley.dist_eq x z
  simp only [gromovProduct, hxw, hyw, hzw, hxy, hyz, hxz]
  exact min_gromov_le_of_fourPoint keyR

/-! ### The converse

The same permutation and the same two cases, read backwards.  Nothing here is
new geometry: `2·(a|b)_w = d(w,a) + d(w,b) - d(a,b)` turns the three Gromov
products at a common basepoint into `T` minus the three pairings, so `min` over
products is `max` over pairings, and the `2δ` written into the four-point
condition is the same `2` that clearing the halves produces.  They cancel, which
is why the constant survives the crossing untouched. -/

/-- **The min form implies the max form**, at six reals and with no constant
lost --- the converse of `min_gromov_le_of_fourPoint`.  In each branch the
comparison of the two pairings decides which argument the `min` attains, and the
difference of the two Gromov products is exactly the difference of the two
pairings. -/
theorem fourPoint_of_min_gromov {dwx dwy dwz dxy dyz dxz e : ℝ}
    (h : min ((dwx + dwy - dxy) / 2) ((dwy + dwz - dyz) / 2) - e
      ≤ (dwx + dwz - dxz) / 2) :
    dwy + dxz ≤ max (dwx + dyz) (dwz + dxy) + 2 * e := by
  rcases le_total (dwx + dyz) (dwz + dxy) with hle | hle
  · rw [min_eq_left (by linarith : (dwx + dwy - dxy) / 2 ≤ (dwy + dwz - dyz) / 2)]
      at h
    rw [max_eq_right hle]
    linarith
  · rw [min_eq_right (by linarith : (dwy + dwz - dyz) / 2 ≤ (dwx + dwy - dxy) / 2)]
      at h
    rw [max_eq_left hle]
    linarith

/-- **A hyperbolic `Γ(G,A)` makes its alphabet four-point hyperbolic**, at the
ceiling of the constant.

The ceiling is the only thing lost: `⌈δ⌉₊` beats `δ` by `Nat.le_ceil`, and the
`2` in front of it is the `2` already in the four-point condition, not a factor
picked up in the crossing.  Together with `isHyperbolicSpace_cayley_of_fourPoint`
this says the two conditions are the same condition. -/
theorem isFourPointHyperbolic_of_isHyperbolicSpace {G : Type u} [Group G]
    (A : Alphabet G) {δ : ℝ} (hδ : IsHyperbolicSpace δ (Cayley A)) :
    Hyperbolic.IsFourPointHyperbolic A.carrier ⌈δ⌉₊ := by
  intro w x y z
  have hS := A.symmetricGenerating
  have key := hδ (Cayley.of A w) (Cayley.of A y) (Cayley.of A x) (Cayley.of A z)
  have hxw : dist (Cayley.of A x) (Cayley.of A w)
      = ((wordDist A.carrier w x : ℕ) : ℝ) := by
    rw [Cayley.dist_eq, Cayley.val_of, Cayley.val_of, wordDist_comm hS]
  have hyw : dist (Cayley.of A y) (Cayley.of A w)
      = ((wordDist A.carrier w y : ℕ) : ℝ) := by
    rw [Cayley.dist_eq, Cayley.val_of, Cayley.val_of, wordDist_comm hS]
  have hzw : dist (Cayley.of A z) (Cayley.of A w)
      = ((wordDist A.carrier w z : ℕ) : ℝ) := by
    rw [Cayley.dist_eq, Cayley.val_of, Cayley.val_of, wordDist_comm hS]
  have hyx : dist (Cayley.of A y) (Cayley.of A x)
      = ((wordDist A.carrier x y : ℕ) : ℝ) := by
    rw [Cayley.dist_eq, Cayley.val_of, Cayley.val_of, wordDist_comm hS]
  have hxz : dist (Cayley.of A x) (Cayley.of A z)
      = ((wordDist A.carrier x z : ℕ) : ℝ) := by
    rw [Cayley.dist_eq, Cayley.val_of, Cayley.val_of]
  have hyz : dist (Cayley.of A y) (Cayley.of A z)
      = ((wordDist A.carrier y z : ℕ) : ℝ) := by
    rw [Cayley.dist_eq, Cayley.val_of, Cayley.val_of]
  simp only [gromovProduct, hxw, hyw, hzw, hyx, hxz, hyz] at key
  have hceil : (δ : ℝ) ≤ ((⌈δ⌉₊ : ℕ) : ℝ) := Nat.le_ceil δ
  have hmain := fourPoint_of_min_gromov key
  have hR : ((wordDist A.carrier w x : ℕ) : ℝ)
        + ((wordDist A.carrier y z : ℕ) : ℝ)
      ≤ max (((wordDist A.carrier w y : ℕ) : ℝ)
              + ((wordDist A.carrier x z : ℕ) : ℝ))
            (((wordDist A.carrier w z : ℕ) : ℝ)
              + ((wordDist A.carrier x y : ℕ) : ℝ))
        + 2 * ((⌈δ⌉₊ : ℕ) : ℝ) := by
    linarith
  exact_mod_cast hR

/-- **The four-point constant a hyperbolically embedded family supplies.**

Dahmani--Guirardel--Osin's Definition 4.25 gives hyperbolicity of
`Γ(G, X ⊔ ⨆H)` in the `ℝ` vocabulary; the whole isolated-component layer of
their §4.2 is stated in the `ℕ` one.  This is the step between, and it is the
reason no consumer of that layer has to carry a four-point hypothesis it cannot
discharge. -/
theorem exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded
    {G : Type u} [Group G] {Λ : Type w} (D : RelGenSet G Λ)
    (hemb : D.IsHyperbolicallyEmbedded) :
    ∃ n : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier n := by
  obtain ⟨δ, hδ⟩ := hemb.hyperbolic
  exact ⟨⌈δ⌉₊, isFourPointHyperbolic_of_isHyperbolicSpace D.alphabet hδ⟩

/-! ## 3.  Farb's clause for the free product, in the `ℕ` vocabulary -/

namespace RelHyp

/-- **The coned-off Cayley graph of `U ∗ H` over the cosets of `U` satisfies the
four-point condition**, at the explicit relative generating set built from the
finite symmetric generating set and constant that `IsHyperbolicGroup H`
supplies.

This is `FreeProductConedHyperbolicStatement` in the vocabulary a word-metric
development produces.  The alphabet in question is
`of_true '' ↑S ∪ of_false '' univ` -- the union alphabet of the two factors,
with the peripheral factor spelled by whole elements -- so a four-point
condition for union alphabets over `CoprodI` in general specialises to it, and
nothing has to be transported between generating sets. -/
def FreeProductConedFourPointStatement : Prop :=
  ∀ (U H : Type) (_ : Group U) (_ : Group H) (S : Finset H)
    (hS : IsSymmetricGeneratingSet (S : Set H)) (δ : ℕ),
      Hyperbolic.IsFourPointHyperbolic (S : Set H) δ →
        ∃ Δ : ℕ, Hyperbolic.IsFourPointHyperbolic
          (freeProductRelGen U H S hS).alphabet.carrier Δ

/-- **Farb's clause, from its `ℕ`-valued form.**  The last mile of
`FreeProductRelativelyHyperbolicStatement`: with
`peripheralMetricLocallyFinite_freeProductRelGen` supplying the
Dahmani--Guirardel--Osin clause, this is all that stands between a four-point
count on the union alphabet and Osin's Theorem 2.34. -/
theorem freeProductConedHyperbolicStatement_of_fourPoint
    (h : FreeProductConedFourPointStatement) :
    FreeProductConedHyperbolicStatement := by
  intro U H instU instH S hS δ hδ
  obtain ⟨Δ, hΔ⟩ := h U H instU instH S hS δ hδ
  exact ⟨(Δ : ℝ), isHyperbolicSpace_cayley_of_fourPoint _ hΔ⟩

/-- **`FreeProductRelativelyHyperbolicStatement` from a four-point count.**  The
whole of Osin, Memoirs 179, Theorem 2.34 now rests on one `ℕ`-valued
combinatorial statement about the union alphabet of a free product. -/
theorem freeProductRelativelyHyperbolicStatement_of_fourPoint
    (h : FreeProductConedFourPointStatement) :
    FreeProductRelativelyHyperbolicStatement :=
  freeProductRelativelyHyperbolicStatement_of_coned
    (freeProductConedHyperbolicStatement_of_fourPoint h)

end RelHyp

end GGT
end GroupApproximation
