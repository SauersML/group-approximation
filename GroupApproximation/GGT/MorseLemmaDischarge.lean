import GroupApproximation.Algebra.MorseLemma
import GroupApproximation.GGT.CayleyFourPointBridge
import GroupApproximation.GGT.CayleyGeodesicRealisation
import GroupApproximation.GGT.ElementaryMorseChord

/-!
# The Morse lemma, discharged

`Hyperbolic.MorseLemma` (`Algebra/MorseLemma.lean`) was stated there as the one
input its lane was missing, and assumed by nothing.  It is a theorem:
`Hyperbolic.morseLemma` below.

## Why it was not available before, and what changed

Two obstructions, both now gone.

**No geodesics.**  `GGT.ElementaryMorse.exists_bound_chain_near_chord` proves the
Morse lemma in any hyperbolic pseudometric space, but needs a genuine
`f : ℝ → X` with `IsGeodesicSegment f 0 L`, and `Cayley A` has none — every
distance in it is a natural number.  That is now repaired one level down:
`GGT.CayleyGeodesicModel.isGeodesicRealisationQuot` proves `PointQuot A`, the
metric identification of the realisation, is a geodesic space, unconditionally
and at a bare `Alphabet`.  (`Point A` itself is not one: its doubled edges put
distinct points at distance zero.)

**The constant was bound under the space.**  `MorseLemma` puts its `∃ R` outside
the `∀ (G : Type)` — one constant for all groups — while the chord lemmas read
`∀ X, ∃ K`, which does not invert.  The constants are in fact space-free, since
they come from `HullGeometry.exists_bound_of_linear_le_add_clog`, whose statement
mentions no space; `GGT.ElementaryMorse.exists_bound_chain_near_chord_uniform`
is that reading, and the space-first form is now a wrapper around it.

## The proof

Given `S` with the four-point condition at `δ`, `GGT.isHyperbolicSpace_cayley_of_fourPoint`
turns it into `IsHyperbolicSpace (δ : ℝ) (Cayley ⟨S, hS⟩)`, and the quotient
realisation `W = PointQuot A` is then a geodesic space, hyperbolic at `δ + 6`,
receiving `Cayley A` by a map of additive distortion `1`.

The chain `m ↦ ι (p m)` inherits its constants from the quasi-geodesic and the
distortion: step `K + C + 1`, progress `l = 1/(K+1)` with additive error
`C + 1`.  The `1/(K+1)` rather than `1/K` is not laziness — at `K = 0` the
quasi-geodesic clause forces the chain constant, and `l` must be positive.

`exists_bound_chain_near_chord_uniform` then puts `ι (p i)` within `K₂` of a
point `f t` of a geodesic joining `ι (p 0)` to `ι (p n)`, with `K₂` fixed before
the group.  What remains is that `MorseLemma` asks for a between-point **of
`G`**, not a point of `W`: take `q` between `p 0` and `p n` at parameter
`min ⌊t⌋₊ (d_S (p 0) (p n))`, which `Hyperbolic.exists_isBetween` supplies, note
that its parameter is within `1` of `t` on either side of the clamp, and close
the gap with one application of the four-point condition in `W` at basepoint
`ι q`.  Pulling back through the distortion gives the bound in `d_S`.

## Model tests

At `n = 0` the chain is a point and `q = p 0` works with distance `0`; the
statement is not vacuous there but carries no content, which is right.  At
`K = 1, C = 0` the hypothesis is a genuine geodesic chain and the conclusion is
the (already available) statement that its vertices are between its endpoints up
to a constant.  The theorem must fail to be provable with `l` replaced by a
constant independent of `K` — and it is not so provable, which is why `1/(K+1)`
appears; that is the check that the quasi-geodesic constant is doing work.
-/

namespace GroupApproximation
namespace Hyperbolic

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## The discharge -/

/-- **The Morse lemma**, proved.

Every point of a `(K,C)`-quasi-geodesic is within a constant of a point lying
between its endpoints, with the constant uniform over all groups and all
symmetric generating sets satisfying the four-point condition at `δ`.

See the module header for the two obstructions this clears and for the shape of
the argument. -/
theorem morseLemma : Hyperbolic.MorseLemma := by
  intro K C delta
  have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hl : (0 : ℝ) < 1 / ((K : ℝ) + 1) := by positivity
  have hD0 : (0 : ℝ) ≤ (K : ℝ) + C + 1 := by positivity
  have hB0 : (0 : ℝ) ≤ (C : ℝ) + 1 := by positivity
  have hd0 : (0 : ℝ) ≤ (delta : ℝ) + 6 := by positivity
  obtain ⟨K₂, hK₂0, hK₂⟩ :=
    GGT.ElementaryMorse.exists_bound_chain_near_chord_uniform
      (δ := (delta : ℝ) + 6) (D := (K : ℝ) + C + 1) (l := 1 / ((K : ℝ) + 1))
      (B := (C : ℝ) + 1) hd0 hD0 hl hB0
  refine ⟨⌈K₂ + 2 * ((delta : ℝ) + 6) + 9⌉₊, ?_⟩
  intro G _ S hS hdelta n p hqg i hi
  set A : Alphabet G := ⟨S, hS⟩ with hA
  have hhyp : IsHyperbolicSpace ((delta : ℝ)) (Cayley A) :=
    GGT.isHyperbolicSpace_cayley_of_fourPoint A hdelta
  have hgeoW : IsGeodesicSpace (GGT.CayleyGeodesicModel.PointQuot A) :=
    GGT.CayleyGeodesicModel.isGeodesicRealisationQuot A
  have hhypW : IsHyperbolicSpace ((delta : ℝ) + 6)
      (GGT.CayleyGeodesicModel.PointQuot A) :=
    GGT.CayleyGeodesicModel.isHyperbolicSpace_pointQuot
      (GGT.CayleyGeodesicModel.isHyperbolicSpace_point A hhyp)
  have hdisto := GGT.CayleyGeodesicModel.hasAdditiveDistortion_iotaQuot A
  set ι : G → GGT.CayleyGeodesicModel.PointQuot A :=
    fun g => GGT.CayleyGeodesicModel.iotaQuot A (Cayley.of A g) with hiota
  have hup : ∀ a b : G, dist (ι a) (ι b) ≤ ((wordDist S a b : ℕ) : ℝ) + 1 := by
    intro a b
    have h := hdisto (Cayley.of A a) (Cayley.of A b)
    have hd : dist (Cayley.of A a) (Cayley.of A b) = ((wordDist S a b : ℕ) : ℝ) :=
      Cayley.dist_eq _ _
    rw [hd] at h
    have h2 := (abs_le.mp h).2
    show dist (GGT.CayleyGeodesicModel.iotaQuot A (Cayley.of A a))
      (GGT.CayleyGeodesicModel.iotaQuot A (Cayley.of A b)) ≤ _
    linarith
  have hlow : ∀ a b : G, ((wordDist S a b : ℕ) : ℝ) - 1 ≤ dist (ι a) (ι b) := by
    intro a b
    have h := hdisto (Cayley.of A a) (Cayley.of A b)
    have hd : dist (Cayley.of A a) (Cayley.of A b) = ((wordDist S a b : ℕ) : ℝ) :=
      Cayley.dist_eq _ _
    rw [hd] at h
    have h1 := (abs_le.mp h).1
    show _ ≤ dist (GGT.CayleyGeodesicModel.iotaQuot A (Cayley.of A a))
      (GGT.CayleyGeodesicModel.iotaQuot A (Cayley.of A b))
    linarith
  set y : ℕ → GGT.CayleyGeodesicModel.PointQuot A := fun m => ι (p m) with hy
  have hstep : ∀ m, m < n → dist (y m) (y (m + 1)) ≤ (K : ℝ) + C + 1 := by
    intro m hm
    have hq : wordDist S (p m) (p (m + 1)) ≤ K * (m + 1 - m) + C :=
      (hqg m (by omega) (m + 1) (by omega) (by omega)).1
    have hsub : m + 1 - m = 1 := by omega
    rw [hsub] at hq
    have hqr : ((wordDist S (p m) (p (m + 1)) : ℕ) : ℝ) ≤ (K : ℝ) + C := by
      have hnat : wordDist S (p m) (p (m + 1)) ≤ K + C := by omega
      exact_mod_cast hnat
    have hu : dist (y m) (y (m + 1)) ≤ ((wordDist S (p m) (p (m + 1)) : ℕ) : ℝ) + 1 :=
      hup (p m) (p (m + 1))
    linarith
  have hprog : ∀ a b : ℕ, a ≤ b → b ≤ n →
      1 / ((K : ℝ) + 1) * ((b - a : ℕ) : ℝ) - ((C : ℝ) + 1) ≤ dist (y a) (y b) := by
    intro a b hab hb
    have hq : b - a ≤ K * (wordDist S (p a) (p b) + C) :=
      (hqg a (by omega) b hb hab).2
    have hqr : ((b - a : ℕ) : ℝ)
        ≤ (K : ℝ) * (((wordDist S (p a) (p b) : ℕ) : ℝ) + (C : ℝ)) := by
      exact_mod_cast hq
    have hw0 : (0 : ℝ) ≤ ((wordDist S (p a) (p b) : ℕ) : ℝ) := by positivity
    have hC0 : (0 : ℝ) ≤ (C : ℝ) := by positivity
    have hKle : (K : ℝ) * (((wordDist S (p a) (p b) : ℕ) : ℝ) + (C : ℝ))
        ≤ ((K : ℝ) + 1) * (((wordDist S (p a) (p b) : ℕ) : ℝ) + (C : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hdiv : 1 / ((K : ℝ) + 1) * ((b - a : ℕ) : ℝ)
        ≤ ((wordDist S (p a) (p b) : ℕ) : ℝ) + (C : ℝ) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hKpos]
      nlinarith
    have hlw : ((wordDist S (p a) (p b) : ℕ) : ℝ) - 1 ≤ dist (y a) (y b) :=
      hlow (p a) (p b)
    linarith
  obtain ⟨f, hf, hf0, hfL⟩ := hgeoW (y 0) (y n)
  have hL0 : (0 : ℝ) ≤ dist (y 0) (y n) := dist_nonneg
  obtain ⟨t, ht, hti⟩ :=
    hK₂ (GGT.CayleyGeodesicModel.PointQuot A) hhypW y n hstep hprog
      (dist (y 0) (y n)) hL0 f hf hf0 hfL i hi
  set Dn : ℕ := wordDist S (p 0) (p n) with hDn
  have hjle : min ⌊t⌋₊ Dn ≤ Dn := min_le_right _ _
  obtain ⟨q, hqbet, hqpar⟩ := Hyperbolic.exists_isBetween hS (p 0) (p n) hjle
  refine ⟨q, hqbet, ?_⟩
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have htL : t ≤ dist (y 0) (y n) := ht.2
  have hfl1 : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
  have hfl2 : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
  have hLub : dist (y 0) (y n) ≤ ((Dn : ℕ) : ℝ) + 1 := hup (p 0) (p n)
  have hLlb : ((Dn : ℕ) : ℝ) - 1 ≤ dist (y 0) (y n) := hlow (p 0) (p n)
  have hjt : ((min ⌊t⌋₊ Dn : ℕ) : ℝ) ≤ t + 1 ∧ t ≤ ((min ⌊t⌋₊ Dn : ℕ) : ℝ) + 1 := by
    rcases le_total (⌊t⌋₊ : ℕ) Dn with hc | hc
    · rw [min_eq_left hc]
      constructor <;> linarith
    · rw [min_eq_right hc]
      have hDnle : ((Dn : ℕ) : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast hc
      constructor <;> linarith
  have hqbet' : wordDist S (p 0) q + wordDist S q (p n) = Dn := hqbet
  have hq0up : dist (y 0) (ι q) ≤ t + 2 := by
    have h1 : dist (ι (p 0)) (ι q) ≤ ((wordDist S (p 0) q : ℕ) : ℝ) + 1 :=
      hup (p 0) q
    rw [hqpar] at h1
    have h1' : dist (y 0) (ι q) ≤ ((min ⌊t⌋₊ Dn : ℕ) : ℝ) + 1 := h1
    linarith [hjt.1]
  have hq0low : t - 2 ≤ dist (y 0) (ι q) := by
    have h2 : ((wordDist S (p 0) q : ℕ) : ℝ) - 1 ≤ dist (ι (p 0)) (ι q) :=
      hlow (p 0) q
    rw [hqpar] at h2
    have h2' : ((min ⌊t⌋₊ Dn : ℕ) : ℝ) - 1 ≤ dist (y 0) (ι q) := h2
    linarith [hjt.2]
  have hqn : dist (ι q) (y n) ≤ ((Dn : ℕ) : ℝ) - ((min ⌊t⌋₊ Dn : ℕ) : ℝ) + 1 := by
    have h1 : dist (ι q) (ι (p n)) ≤ ((wordDist S q (p n) : ℕ) : ℝ) + 1 :=
      hup q (p n)
    have hnat : wordDist S q (p n) = Dn - min ⌊t⌋₊ Dn := by omega
    rw [hnat] at h1
    have hcast : ((Dn - min ⌊t⌋₊ Dn : ℕ) : ℝ)
        = ((Dn : ℕ) : ℝ) - ((min ⌊t⌋₊ Dn : ℕ) : ℝ) := by
      rw [Nat.cast_sub hjle]
    rw [hcast] at h1
    exact h1
  have hkey : dist (f t) (ι q) ≤ 2 * ((delta : ℝ) + 6) + 8 := by
    have h4 := hhypW (ι q) (y 0) (f t) (y n)
    have e1 : dist (y 0) (f t) = t := by
      have hd := hf 0 ⟨le_refl 0, hL0⟩ t ht
      rw [hf0] at hd
      rw [hd, abs_of_nonpos (by linarith)]
      ring
    have e2 : dist (f t) (y n) = dist (y 0) (y n) - t := by
      have hd := hf t ht (dist (y 0) (y n)) ⟨hL0, le_refl _⟩
      rw [hfL] at hd
      rw [hd, abs_of_nonpos (by linarith)]
      ring
    have hqnlow : dist (y 0) (y n) - dist (y 0) (ι q) ≤ dist (ι q) (y n) := by
      have htri := dist_triangle (y 0) (ι q) (y n)
      linarith
    simp only [gromovProduct] at h4
    have c1 : dist (y 0) (ι q) = dist (ι q) (y 0) := dist_comm _ _
    have c2 : dist (f t) (ι q) = dist (ι q) (f t) := dist_comm _ _
    have c3 : dist (y n) (ι q) = dist (ι q) (y n) := dist_comm _ _
    have c4 : dist (y 0) (f t) = dist (f t) (y 0) := dist_comm _ _
    have c5 : dist (f t) (y n) = dist (y n) (f t) := dist_comm _ _
    rcases le_total
        ((dist (y 0) (ι q) + dist (f t) (ι q) - dist (y 0) (f t)) / 2)
        ((dist (f t) (ι q) + dist (y n) (ι q) - dist (f t) (y n)) / 2) with hm | hm
    · rw [min_eq_left hm] at h4
      linarith [hjt.1, hjt.2]
    · rw [min_eq_right hm] at h4
      linarith [hjt.1, hjt.2]
  have hchain : dist (y i) (ι q) ≤ K₂ + (2 * ((delta : ℝ) + 6) + 8) := by
    have htri := dist_triangle (y i) (f t) (ι q)
    linarith
  have hfinal : ((wordDist S (p i) q : ℕ) : ℝ)
      ≤ K₂ + 2 * ((delta : ℝ) + 6) + 9 := by
    have h : ((wordDist S (p i) q : ℕ) : ℝ) - 1 ≤ dist (ι (p i)) (ι q) :=
      hlow (p i) q
    have h' : ((wordDist S (p i) q : ℕ) : ℝ) - 1 ≤ dist (y i) (ι q) := h
    linarith
  have hceil : K₂ + 2 * ((delta : ℝ) + 6) + 9
      ≤ ((⌈K₂ + 2 * ((delta : ℝ) + 6) + 9⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hcast : ((wordDist S (p i) q : ℕ) : ℝ)
      ≤ ((⌈K₂ + 2 * ((delta : ℝ) + 6) + 9⌉₊ : ℕ) : ℝ) := by linarith
  exact_mod_cast hcast

end Hyperbolic
end GroupApproximation
