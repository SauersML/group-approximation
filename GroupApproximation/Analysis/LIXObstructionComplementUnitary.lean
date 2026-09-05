import Mathlib

/-!
# From "the complements are isomorphic" to a unitary automorphism carrying `e` to `s`

Lane `lix-obstruction`, campaign target 3 (STW Problem LIX).

In the proof of Lemma 2 of
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`
the bundle `V = 1³ ⊕ H` carries two unit sections `e` and `s`, and the argument
opens with:

> Suppose these complements were isomorphic.  Polar decomposition of an
> isomorphism produces a unitary isomorphism between them.  Extending it by
> `e ↦ s` yields a unitary bundle automorphism `g` of `V` satisfying `g e = s`.

In the projection model of the campaign a bundle isomorphism **is** a
Murray–von Neumann equivalence of projections, i.e. it is already given by a
partial isometry.  So the polar decomposition step costs nothing, and the whole
paragraph becomes the following piece of `*`-ring algebra: *two partial
isometries with complementary source and range projections add up to a unitary
of the corner.*  That is `unitary_of_complementary_partialIsometry` below, and
`mvn_complement_unitary_apply_eq` is the form the manuscript uses, where the
first partial isometry is the elementary `s * star e`.

Nothing here is analytic: the statements hold in a bare `Ring` with a
`StarRing`, hence verbatim in `Matrix (Fin N) (Fin N) C(X, ℂ)`.

## Main results

* `unitary_of_complementary_partialIsometry` — `w₀ + w₁` is a unitary of the
  corner `P A P`, and it conjugates `p` to `q`.
* `mvn_complement_unitary_apply_eq` — the manuscript's `g`, with `g * e = s`.
-/

namespace GroupApproximation
namespace STW59

variable {A : Type*} [Ring A] [StarRing A]

/-! ### Elementary partial-isometry algebra

Throughout, a *partial isometry* is an element `w` with `w * star w * w = w`.
Its source projection is `star w * w` and its range projection is `w * star w`;
both are genuine projections, and `w` is fixed on both sides by them. -/

section PartialIsometry

variable {w : A}

theorem isSelfAdjoint_mul_star_self (w : A) : star (w * star w) = w * star w := by
  rw [star_mul, star_star]

theorem isSelfAdjoint_star_mul_self (w : A) : star (star w * w) = star w * w := by
  rw [star_mul, star_star]

theorem mul_star_self_idem (hw : w * star w * w = w) :
    (w * star w) * (w * star w) = w * star w := by
  rw [mul_assoc w (star w) (w * star w), ← mul_assoc (star w) w (star w),
    ← mul_assoc w (star w * w) (star w), ← mul_assoc w (star w) w, hw]

theorem star_mul_self_idem (hw : w * star w * w = w) :
    (star w * w) * (star w * w) = star w * w := by
  rw [mul_assoc (star w) w (star w * w), ← mul_assoc w (star w) w, hw]

theorem mul_star_mul_self_left (hw : w * star w * w = w) : (w * star w) * w = w := hw

theorem mul_star_mul_self_right (hw : w * star w * w = w) : w * (star w * w) = w := by
  rw [← mul_assoc]; exact hw

theorem star_mul_star_self_left (hw : w * star w * w = w) :
    star w * (w * star w) = star w := by
  have := congrArg star hw
  simpa [star_mul, mul_assoc] using this

end PartialIsometry

/-! ### The unitary of the corner -/

/-- **Two partial isometries with complementary source and range projections add up to a
unitary of the corner.**

`w₀` implements `p ~ q` and `w₁` implements `P - p ~ P - q`, all inside the corner
determined by the projection `P`.  Then `g = w₀ + w₁` satisfies `star g * g = P`,
`g * star g = P` (so `g` is a unitary of `P A P`) and `g * p * star g = q`.

This is the projection-model replacement for the manuscript's polar-decomposition
step: Murray–von Neumann equivalence already supplies the partial isometries, so no
polar decomposition and no functional calculus are needed. -/
theorem unitary_of_complementary_partialIsometry
    {P p q w₀ w₁ : A}
    (hPstar : star P = P)
    (hPp : P * p = p) (hpP : p * P = p)
    (hPq : P * q = q) (hqP : q * P = q)
    (h₀src : star w₀ * w₀ = p) (h₀rng : w₀ * star w₀ = q) (h₀pi : w₀ * star w₀ * w₀ = w₀)
    (h₁src : star w₁ * w₁ = P - p) (h₁rng : w₁ * star w₁ = P - q)
    (h₁pi : w₁ * star w₁ * w₁ = w₁) :
    star (w₀ + w₁) * (w₀ + w₁) = P ∧ (w₀ + w₁) * star (w₀ + w₁) = P ∧
      (w₀ + w₁) * p * star (w₀ + w₁) = q := by
  -- `q` is idempotent, and `w₀` is fixed by its range projection on the left.
  have hqq : q * q = q := by rw [← h₀rng]; exact mul_star_self_idem h₀pi
  have hpp : p * p = p := by rw [← h₀src]; exact star_mul_self_idem h₀pi
  have hqw₀ : q * w₀ = w₀ := by rw [← h₀rng]; exact mul_star_mul_self_left h₀pi
  have hw₀p : w₀ * p = w₀ := by rw [← h₀src]; exact mul_star_mul_self_right h₀pi
  have hw₁ : w₁ * (P - p) = w₁ := by rw [← h₁src]; exact mul_star_mul_self_right h₁pi
  have hw₁' : (P - q) * w₁ = w₁ := by rw [← h₁rng]; exact mul_star_mul_self_left h₁pi
  -- `star w₀` absorbs `q` on the right, hence `P` on the right.
  have hsw₀q : star w₀ * q = star w₀ := by
    have := congrArg star hqw₀
    rwa [star_mul, ← h₀rng, isSelfAdjoint_mul_star_self, h₀rng] at this
  have hsw₀P : star w₀ * P = star w₀ := by
    calc star w₀ * P = (star w₀ * q) * P := by rw [hsw₀q]
      _ = star w₀ * (q * P) := by rw [mul_assoc]
      _ = star w₀ * q := by rw [hqP]
      _ = star w₀ := hsw₀q
  have hw₀sp : p * star w₀ = star w₀ := by
    have := congrArg star hw₀p
    rwa [star_mul, ← h₀src, isSelfAdjoint_star_mul_self, h₀src] at this
  have hPsw₀ : P * star w₀ = star w₀ := by
    calc P * star w₀ = P * (p * star w₀) := by rw [hw₀sp]
      _ = (P * p) * star w₀ := by rw [mul_assoc]
      _ = p * star w₀ := by rw [hPp]
      _ = star w₀ := hw₀sp
  -- the two cross terms vanish
  have hcross₁ : star w₀ * w₁ = 0 := by
    calc star w₀ * w₁ = star w₀ * ((P - q) * w₁) := by rw [hw₁']
      _ = (star w₀ * (P - q)) * w₁ := by rw [mul_assoc]
      _ = (star w₀ * P - star w₀ * q) * w₁ := by rw [mul_sub]
      _ = 0 := by rw [hsw₀P, hsw₀q, sub_self, zero_mul]
  have hcross₂ : star w₁ * w₀ = 0 := by
    have hsw₁q : star w₁ * q = 0 := by
      have hsw₁ : star w₁ * (P - q) = star w₁ := by
        have := congrArg star hw₁'
        rwa [star_mul, star_sub, hPstar, ← h₀rng, isSelfAdjoint_mul_star_self, h₀rng] at this
      calc star w₁ * q = (star w₁ * (P - q)) * q := by rw [hsw₁]
        _ = star w₁ * ((P - q) * q) := by rw [mul_assoc]
        _ = star w₁ * (P * q - q * q) := by rw [sub_mul]
        _ = 0 := by rw [hPq, hqq, sub_self, mul_zero]
    calc star w₁ * w₀ = star w₁ * (q * w₀) := by rw [hqw₀]
      _ = (star w₁ * q) * w₀ := by rw [mul_assoc]
      _ = 0 := by rw [hsw₁q, zero_mul]
  have hcross₃ : w₀ * star w₁ = 0 := by
    have := congrArg star hcross₂
    simpa [star_mul] using this
  have hcross₄ : w₁ * star w₀ = 0 := by
    have := congrArg star hcross₁
    simpa [star_mul] using this
  -- `w₁` kills `p` on the right
  have hw₁p : w₁ * p = 0 := by
    calc w₁ * p = (w₁ * (P - p)) * p := by rw [hw₁]
      _ = w₁ * ((P - p) * p) := by rw [mul_assoc]
      _ = w₁ * (P * p - p * p) := by rw [sub_mul]
      _ = 0 := by rw [hPp, hpp, sub_self, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · calc star (w₀ + w₁) * (w₀ + w₁)
        = star w₀ * w₀ + star w₀ * w₁ + (star w₁ * w₀ + star w₁ * w₁) := by
          rw [star_add]; ring
      _ = P := by rw [h₀src, h₁src, hcross₁, hcross₂]; ring
  · calc (w₀ + w₁) * star (w₀ + w₁)
        = w₀ * star w₀ + w₀ * star w₁ + (w₁ * star w₀ + w₁ * star w₁) := by
          rw [star_add]; ring
      _ = P := by rw [h₀rng, h₁rng, hcross₃, hcross₄]; ring
  · have hgp : (w₀ + w₁) * p = w₀ := by rw [add_mul, hw₀p, hw₁p, add_zero]
    calc (w₀ + w₁) * p * star (w₀ + w₁) = w₀ * (star w₀ + star w₁) := by
          rw [hgp, star_add]
      _ = w₀ * star w₀ + w₀ * star w₁ := by rw [mul_add]
      _ = q := by rw [h₀rng, hcross₃, add_zero]

/-! ### The manuscript's `g`, with `g e = s`

`e` and `s` are the two unit sections of `V`; `r` is the rank-one projection they
are both partial isometries *from* (in the matrix picture, `e` is the column vector
`e` regarded as a matrix supported in one column, and `r` is the projection onto
that column).  Their range projections are `p = e eᴴ` and `q = s sᴴ`, the projections
onto the lines they span. -/

/-- **Extending an equivalence of the complements by `e ↦ s`.**

Given the equivalence `w₁ : P - e eᴴ ~ P - s sᴴ` of the complements, the element
`g = s * star e + w₁` is a unitary of the corner `P A P` with `g * e = s`.  This is
exactly the automorphism `g` of the manuscript's proof of Lemma 2. -/
theorem mvn_complement_unitary_apply_eq
    {P r e s w₁ : A}
    (hPstar : star P = P)
    (hePi : e * star e * e = e) (hsPi : s * star s * s = s)
    (heSrc : star e * e = r) (hsSrc : star s * s = r)
    (hPe : P * e = e) (hPs : P * s = s)
    (heP : e * star e * P = e * star e) (hsP : s * star s * P = s * star s)
    (h₁src : star w₁ * w₁ = P - e * star e) (h₁rng : w₁ * star w₁ = P - s * star s)
    (h₁pi : w₁ * star w₁ * w₁ = w₁) :
    star (s * star e + w₁) * (s * star e + w₁) = P ∧
      (s * star e + w₁) * star (s * star e + w₁) = P ∧
      (s * star e + w₁) * e = s := by
  have her : e * r = e := by rw [← heSrc, ← mul_assoc]; exact hePi
  have hsr : s * r = s := by rw [← hsSrc, ← mul_assoc]; exact hsPi
  have h₀src : star (s * star e) * (s * star e) = e * star e := by
    calc star (s * star e) * (s * star e) = e * ((star s * s) * star e) := by
          rw [star_mul, star_star]; noncomm_ring
      _ = (e * r) * star e := by rw [hsSrc, mul_assoc]
      _ = e * star e := by rw [her]
  have h₀rng : (s * star e) * star (s * star e) = s * star s := by
    calc (s * star e) * star (s * star e) = s * ((star e * e) * star s) := by
          rw [star_mul, star_star]; noncomm_ring
      _ = (s * r) * star s := by rw [heSrc, mul_assoc]
      _ = s * star s := by rw [hsr]
  have h₀pi : (s * star e) * star (s * star e) * (s * star e) = s * star e := by
    rw [h₀rng]
    calc s * star s * (s * star e) = (s * star s * s) * star e := by rw [mul_assoc]
      _ = s * star e := by rw [hsPi]
  have hmain := unitary_of_complementary_partialIsometry (P := P) (p := e * star e)
    (q := s * star s) (w₀ := s * star e) (w₁ := w₁) hPstar
    (by rw [← mul_assoc, hPe]) heP (by rw [← mul_assoc, hPs]) hsP
    h₀src h₀rng h₀pi h₁src h₁rng h₁pi
  refine ⟨hmain.1, hmain.2.1, ?_⟩
  have hw₁e : w₁ * e = 0 := by
    have hw₁ : w₁ * (P - e * star e) = w₁ := by
      rw [← h₁src, ← mul_assoc]; exact h₁pi
    calc w₁ * e = (w₁ * (P - e * star e)) * e := by rw [hw₁]
      _ = w₁ * ((P - e * star e) * e) := by rw [mul_assoc]
      _ = w₁ * (P * e - e * star e * e) := by rw [sub_mul]
      _ = 0 := by rw [hPe, hePi, sub_self, mul_zero]
  calc (s * star e + w₁) * e = s * (star e * e) + w₁ * e := by rw [add_mul, mul_assoc]
    _ = s := by rw [heSrc, hsr, hw₁e, add_zero]

end STW59
end GroupApproximation
