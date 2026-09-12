import Mathlib
import GroupApproximation.Analysis.LIXClutching

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

open scoped Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

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
  have hassoc : (w * star w) * (w * star w) = (w * star w * w) * star w := by
    noncomm_ring
  rw [hassoc, hw]

theorem star_mul_self_idem (hw : w * star w * w = w) :
    (star w * w) * (star w * w) = star w * w := by
  have hassoc : (star w * w) * (star w * w) = star w * (w * star w * w) := by
    noncomm_ring
  rw [hassoc, hw]

theorem mul_star_mul_self_left (hw : w * star w * w = w) : (w * star w) * w = w := hw

theorem mul_star_mul_self_right (hw : w * star w * w = w) : w * (star w * w) = w := by
  rw [← mul_assoc]; exact hw

/-- Adjointing a partial isometry gives one, and this is the identity used to move
`star w` past its own projections. -/
theorem star_mul_star_self_left (hw : w * star w * w = w) :
    star w * (w * star w) = star w := by
  have h := congrArg star hw
  rw [star_mul, star_mul, star_star] at h
  exact h

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
    (hPp : P * p = p)
    (hPq : P * q = q) (hqP : q * P = q)
    (h₀src : star w₀ * w₀ = p) (h₀rng : w₀ * star w₀ = q) (h₀pi : w₀ * star w₀ * w₀ = w₀)
    (h₁src : star w₁ * w₁ = P - p) (h₁rng : w₁ * star w₁ = P - q)
    (h₁pi : w₁ * star w₁ * w₁ = w₁) :
    star (w₀ + w₁) * (w₀ + w₁) = P ∧ (w₀ + w₁) * star (w₀ + w₁) = P ∧
      (w₀ + w₁) * p * star (w₀ + w₁) = q := by
  -- `p` and `q` are idempotent, and `w₀` is fixed by its two projections.
  have hqq : q * q = q := by rw [← h₀rng]; exact mul_star_self_idem h₀pi
  have hpp : p * p = p := by rw [← h₀src]; exact star_mul_self_idem h₀pi
  have hqw₀ : q * w₀ = w₀ := by rw [← h₀rng]; exact mul_star_mul_self_left h₀pi
  have hw₀p : w₀ * p = w₀ := by rw [← h₀src]; exact mul_star_mul_self_right h₀pi
  have hw₁ : w₁ * (P - p) = w₁ := by rw [← h₁src]; exact mul_star_mul_self_right h₁pi
  have hw₁' : (P - q) * w₁ = w₁ := by rw [← h₁rng]; exact mul_star_mul_self_left h₁pi
  -- `star w₀` absorbs `q` on the right, hence `P` on the right.
  have hsw₀q : star w₀ * q = star w₀ := by
    have h := congrArg star hqw₀
    rwa [star_mul, ← h₀rng, isSelfAdjoint_mul_star_self, h₀rng] at h
  have hsw₀P : star w₀ * P = star w₀ := by
    calc star w₀ * P = (star w₀ * q) * P := by rw [hsw₀q]
      _ = star w₀ * (q * P) := by rw [mul_assoc]
      _ = star w₀ * q := by rw [hqP]
      _ = star w₀ := hsw₀q
  have hpsw₀ : p * star w₀ = star w₀ := by
    have h := congrArg star hw₀p
    rwa [star_mul, ← h₀src, isSelfAdjoint_star_mul_self, h₀src] at h
  -- `w₁` kills `p` on the right.
  have hw₁p : w₁ * p = 0 := by
    calc w₁ * p = (w₁ * (P - p)) * p := by rw [hw₁]
      _ = w₁ * ((P - p) * p) := by rw [mul_assoc]
      _ = w₁ * (P * p - p * p) := by rw [sub_mul]
      _ = 0 := by rw [hPp, hpp, sub_self, mul_zero]
  -- the four cross terms vanish
  have hcross₁ : star w₀ * w₁ = 0 := by
    calc star w₀ * w₁ = star w₀ * ((P - q) * w₁) := by rw [hw₁']
      _ = (star w₀ * (P - q)) * w₁ := by rw [mul_assoc]
      _ = (star w₀ * P - star w₀ * q) * w₁ := by rw [mul_sub]
      _ = 0 := by rw [hsw₀P, hsw₀q, sub_self, zero_mul]
  have hcross₂ : star w₁ * w₀ = 0 := by
    have hsw₁ : star w₁ * (P - q) = star w₁ := by
      have h := congrArg star hw₁'
      rwa [star_mul, star_sub, hPstar, ← h₀rng, isSelfAdjoint_mul_star_self, h₀rng] at h
    have hsw₁q : star w₁ * q = 0 := by
      calc star w₁ * q = (star w₁ * (P - q)) * q := by rw [hsw₁]
        _ = star w₁ * ((P - q) * q) := by rw [mul_assoc]
        _ = star w₁ * (P * q - q * q) := by rw [sub_mul]
        _ = 0 := by rw [hPq, hqq, sub_self, mul_zero]
    calc star w₁ * w₀ = star w₁ * (q * w₀) := by rw [hqw₀]
      _ = (star w₁ * q) * w₀ := by rw [mul_assoc]
      _ = 0 := by rw [hsw₁q, zero_mul]
  have hcross₄ : w₁ * star w₀ = 0 := by
    calc w₁ * star w₀ = w₁ * (p * star w₀) := by rw [hpsw₀]
      _ = (w₁ * p) * star w₀ := by rw [mul_assoc]
      _ = 0 := by rw [hw₁p, zero_mul]
  have hcross₃ : w₀ * star w₁ = 0 := by
    have h := congrArg star hcross₄
    rwa [star_mul, star_star, star_zero] at h
  refine ⟨?_, ?_, ?_⟩
  · calc star (w₀ + w₁) * (w₀ + w₁)
        = star w₀ * w₀ + star w₀ * w₁ + (star w₁ * w₀ + star w₁ * w₁) := by
          rw [star_add]; noncomm_ring
      _ = P := by rw [h₀src, h₁src, hcross₁, hcross₂]; abel
  · calc (w₀ + w₁) * star (w₀ + w₁)
        = w₀ * star w₀ + w₀ * star w₁ + (w₁ * star w₀ + w₁ * star w₁) := by
          rw [star_add]; noncomm_ring
      _ = P := by rw [h₀rng, h₁rng, hcross₃, hcross₄]; abel
  · have hgp : (w₀ + w₁) * p = w₀ := by rw [add_mul, hw₀p, hw₁p, add_zero]
    calc (w₀ + w₁) * p * star (w₀ + w₁) = w₀ * (star w₀ + star w₁) := by
          rw [hgp, star_add]
      _ = w₀ * star w₀ + w₀ * star w₁ := by rw [mul_add]
      _ = q := by rw [h₀rng, hcross₃, add_zero]

/-! ### The manuscript's `g`, with `g e = s`

`e` and `s` are the two unit sections of `V`; `r` is the projection they are both
partial isometries *from* (in the matrix picture, `e` is the column vector `e`
regarded as a matrix supported in one column, and `r` is the projection onto that
column).  Their range projections are `p = e eᴴ` and `q = s sᴴ`, the projections onto
the lines they span. -/

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
    (hsP : s * star s * P = s * star s)
    (h₁src : star w₁ * w₁ = P - e * star e) (h₁rng : w₁ * star w₁ = P - s * star s)
    (h₁pi : w₁ * star w₁ * w₁ = w₁) :
    star (s * star e + w₁) * (s * star e + w₁) = P ∧
      (s * star e + w₁) * star (s * star e + w₁) = P ∧
      (s * star e + w₁) * e = s := by
  have her : e * r = e := by rw [← heSrc, ← mul_assoc]; exact hePi
  have hsr : s * r = s := by rw [← hsSrc, ← mul_assoc]; exact hsPi
  have h₀src : star (s * star e) * (s * star e) = e * star e := by
    have hassoc : (e * star s) * (s * star e) = e * ((star s * s) * star e) := by
      noncomm_ring
    calc star (s * star e) * (s * star e) = (e * star s) * (s * star e) := by
          rw [star_mul, star_star]
      _ = e * ((star s * s) * star e) := hassoc
      _ = (e * r) * star e := by rw [hsSrc, mul_assoc]
      _ = e * star e := by rw [her]
  have h₀rng : (s * star e) * star (s * star e) = s * star s := by
    have hassoc : (s * star e) * (e * star s) = s * ((star e * e) * star s) := by
      noncomm_ring
    calc (s * star e) * star (s * star e) = (s * star e) * (e * star s) := by
          rw [star_mul, star_star]
      _ = s * ((star e * e) * star s) := hassoc
      _ = (s * r) * star s := by rw [heSrc, mul_assoc]
      _ = s * star s := by rw [hsr]
  have h₀pi : (s * star e) * star (s * star e) * (s * star e) = s * star e := by
    have hassoc : s * star s * (s * star e) = (s * star s * s) * star e := by
      noncomm_ring
    rw [h₀rng, hassoc, hsPi]
  have hmain := unitary_of_complementary_partialIsometry (P := P) (p := e * star e)
    (q := s * star s) (w₀ := s * star e) (w₁ := w₁) hPstar
    (by rw [← mul_assoc, hPe]) (by rw [← mul_assoc, hPs]) hsP
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

/-! ### The continuous-family form (Step A)

`mvn_complement_unitary_apply_eq` is pointwise algebra.  The mapping-torus lane (`cc-lix-odd`)
consumes it over a *parameter space* `M`: `V`, `e`, `s`, `w₁` are all continuous families, and the
corner unitary `g` produced has to be continuous too, since it feeds a continuous bundle
construction downstream.  The premise records the equivalence of the complementary projections
via an *explicit continuous* implementer `w₁` rather than the bare existential
`MurrayVonNeumannEquiv`: an equivalence produced by a discontinuous choice of partial isometry
could not be fed to a continuous construction anyway, so nothing is lost by asking for the
witness up front, and this is recorded against the plainer reading in the lane report. -/

section ContinuousFamily

variable {A : Type*} [Ring A] [StarRing A] [TopologicalSpace A] [ContinuousStar A]
  [ContinuousAdd A] [ContinuousMul A] {M : Type*} [TopologicalSpace M]

/-- **Step A, generic continuous-family form.**  If the ring-level hypotheses of
`mvn_complement_unitary_apply_eq` hold at every point of `M`, with `P`, `e`, `s`, `w₁` all
continuous, then the corner unitary `g = s * star e + w₁` is continuous too. -/
theorem exists_continuous_unitary_corner_apply_eq
    {P r e s w₁ : M → A}
    (hecont : Continuous e) (hscont : Continuous s) (hw₁cont : Continuous w₁)
    (hPstar : ∀ m, star (P m) = P m)
    (hePi : ∀ m, e m * star (e m) * e m = e m) (hsPi : ∀ m, s m * star (s m) * s m = s m)
    (heSrc : ∀ m, star (e m) * e m = r m) (hsSrc : ∀ m, star (s m) * s m = r m)
    (hPe : ∀ m, P m * e m = e m) (hPs : ∀ m, P m * s m = s m)
    (hsP : ∀ m, s m * star (s m) * P m = s m * star (s m))
    (h₁src : ∀ m, star (w₁ m) * w₁ m = P m - e m * star (e m))
    (h₁rng : ∀ m, w₁ m * star (w₁ m) = P m - s m * star (s m))
    (h₁pi : ∀ m, w₁ m * star (w₁ m) * w₁ m = w₁ m) :
    ∃ g : M → A, Continuous g ∧
      (∀ m, star (g m) * g m = P m) ∧ (∀ m, g m * star (g m) = P m) ∧
      (∀ m, g m * e m = s m) :=
  ⟨fun m => s m * star (e m) + w₁ m, (hscont.mul hecont.star).add hw₁cont,
    fun m => (mvn_complement_unitary_apply_eq (hPstar m) (hePi m) (hsPi m) (heSrc m)
      (hsSrc m) (hPe m) (hPs m) (hsP m) (h₁src m) (h₁rng m) (h₁pi m)).1,
    fun m => (mvn_complement_unitary_apply_eq (hPstar m) (hePi m) (hsPi m) (heSrc m)
      (hsSrc m) (hPe m) (hPs m) (hsP m) (h₁src m) (h₁rng m) (h₁pi m)).2.1,
    fun m => (mvn_complement_unitary_apply_eq (hPstar m) (hePi m) (hsPi m) (heSrc m)
      (hsSrc m) (hPe m) (hPs m) (hsP m) (h₁src m) (h₁rng m) (h₁pi m)).2.2⟩

end ContinuousFamily

/-! ### Step A, the vector form the mapping-torus lane consumes

`e`, `s` there are unit *vectors* of `ℂ^K`, not ring elements: `colAt` is the embedding of a
vector into the matrix ring `Matrix K K ℂ` supported on one column, which turns a vector-level
unit section into the ring element `mvn_complement_unitary_apply_eq` needs, and every algebraic
hypothesis of Step A's vector form reduces to a fact about `colAt` proved below. -/

section VectorForm

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The matrix supported on column `k0`, whose column `k0` is the vector `v` and every other
column is zero. -/
def colAt (k0 : K) (v : K → ℂ) : Matrix K K ℂ :=
  Matrix.of fun i j => if j = k0 then v i else 0

theorem colAt_apply (k0 : K) (v : K → ℂ) (i j : K) :
    colAt k0 v i j = if j = k0 then v i else 0 := rfl

/-- The entrywise form of `M *ᵥ v`.  Mathlib at this pin has no `mulVec_apply_eq_sum`:
`mulVec_eq_sum` is the vector-level identity `M *ᵥ v = ∑ i, op (v i) • Mᵀ i`, which is not
what an entrywise computation wants.  This is the definitional unfolding of `mulVec`
through `dotProduct`. -/
theorem mulVec_apply_sum (M : Matrix K K ℂ) (v : K → ℂ) (i : K) :
    (M *ᵥ v) i = ∑ j, M i j * v j := rfl

omit [Fintype K] in
theorem continuous_colAt {M : Type*} [TopologicalSpace M] (k0 : K) {v : M → K → ℂ}
    (hv : Continuous v) : Continuous fun m => colAt k0 (v m) := by
  refine continuous_matrix fun i j => ?_
  simp only [colAt_apply]
  by_cases h : j = k0
  · simp only [if_pos h]
    exact (continuous_apply i).comp hv
  · simp only [if_neg h]
    exact continuous_const

/-- `colAt` turns left multiplication by a matrix into the matrix-vector product. -/
theorem mul_colAt (k0 : K) (M : Matrix K K ℂ) (v : K → ℂ) :
    M * colAt k0 v = colAt k0 (M *ᵥ v) := by
  ext i j
  simp only [Matrix.mul_apply, colAt_apply, mulVec_apply_sum]
  by_cases h : j = k0 <;> simp [h]

theorem mul_colAt_of_mulVec_eq {M : Matrix K K ℂ} {v : K → ℂ} (h : M *ᵥ v = v) (k0 : K) :
    M * colAt k0 v = colAt k0 v := by rw [mul_colAt, h]

theorem colAt_conjTranspose_apply (k0 : K) (v : K → ℂ) (i j : K) :
    (colAt k0 v)ᴴ i j = if i = k0 then star (v j) else 0 := by
  rw [Matrix.conjTranspose_apply, colAt_apply]
  by_cases h : i = k0 <;> simp [h]

theorem colAt_mul_colAt_conjTranspose_apply (k0 : K) (v : K → ℂ) (i j : K) :
    (colAt k0 v * (colAt k0 v)ᴴ) i j = v i * star (v j) := by
  simp only [Matrix.mul_apply, colAt_apply, colAt_conjTranspose_apply]
  rw [Finset.sum_eq_single k0]
  · simp
  · intro b _ hb; simp [hb]
  · intro hb; exact absurd (Finset.mem_univ k0) hb

/-- **The Gram identity is the same for two unit vectors.**  This is `heSrc = hsSrc` (both equal
`r := (colAt k0 e)ᴴ * colAt k0 e`) in `mvn_complement_unitary_apply_eq`, proved directly rather
than by computing a closed form for either side. -/
theorem colAt_conjTranspose_mul_colAt_eq_of_normSq_eq {v w : K → ℂ}
    (h : ∑ i, star (v i) * v i = ∑ i, star (w i) * w i) (k0 : K) :
    (colAt k0 v)ᴴ * colAt k0 v = (colAt k0 w)ᴴ * colAt k0 w := by
  ext i j
  simp only [Matrix.mul_apply, colAt_conjTranspose_apply, colAt_apply]
  by_cases hi : i = k0
  · by_cases hj : j = k0
    · have e1 : (∑ l : K, (if i = k0 then star (v l) else 0) * if j = k0 then v l else 0)
          = ∑ l : K, star (v l) * v l :=
        Finset.sum_congr rfl fun l _ => by rw [if_pos hi, if_pos hj]
      have e2 : (∑ l : K, (if i = k0 then star (w l) else 0) * if j = k0 then w l else 0)
          = ∑ l : K, star (w l) * w l :=
        Finset.sum_congr rfl fun l _ => by rw [if_pos hi, if_pos hj]
      rw [e1, e2, h]
    · have e1 : (∑ l : K, (if i = k0 then star (v l) else 0) * if j = k0 then v l else 0) = 0 :=
        Finset.sum_eq_zero fun l _ => by rw [if_neg hj, mul_zero]
      have e2 : (∑ l : K, (if i = k0 then star (w l) else 0) * if j = k0 then w l else 0) = 0 :=
        Finset.sum_eq_zero fun l _ => by rw [if_neg hj, mul_zero]
      rw [e1, e2]
  · have e1 : (∑ l : K, (if i = k0 then star (v l) else 0) * if j = k0 then v l else 0) = 0 :=
      Finset.sum_eq_zero fun l _ => by rw [if_neg hi, zero_mul]
    have e2 : (∑ l : K, (if i = k0 then star (w l) else 0) * if j = k0 then w l else 0) = 0 :=
      Finset.sum_eq_zero fun l _ => by rw [if_neg hi, zero_mul]
    rw [e1, e2]

theorem colAt_pi_of_normSq_one {v : K → ℂ} (hv : ∑ i, star (v i) * v i = 1) (k0 : K) :
    colAt k0 v * (colAt k0 v)ᴴ * colAt k0 v = colAt k0 v := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [colAt_mul_colAt_conjTranspose_apply, colAt_apply]
  by_cases hj : j = k0
  · rw [if_pos hj]
    have e1 : (∑ l : K, v i * star (v l) * if j = k0 then v l else 0)
        = v i * ∑ l : K, star (v l) * v l := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [if_pos hj]; ring
    rw [e1, hv, mul_one]
  · rw [if_neg hj]
    exact Finset.sum_eq_zero fun l _ => by rw [if_neg hj, mul_zero]

/-- **The corner absorption identity `s · star s · P = s · star s`.**  Needs `P` self-adjoint
and `P *ᵥ v = v`; this is `hsP` at the vector level. -/
theorem colAt_mul_colAt_conjTranspose_mul_of_selfAdjoint_of_mulVec_eq {M : Matrix K K ℂ}
    {v : K → ℂ} (hM : Mᴴ = M) (h : M *ᵥ v = v) (k0 : K) :
    colAt k0 v * (colAt k0 v)ᴴ * M = colAt k0 v * (colAt k0 v)ᴴ := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [colAt_mul_colAt_conjTranspose_apply]
  have hcol : ∀ l : K, M l j = star (M j l) := fun l =>
    (congrFun₂ hM l j).symm.trans (Matrix.conjTranspose_apply M j l)
  have hsum : (∑ l : K, star (v l) * M l j) = star (v j) := by
    calc ∑ l : K, star (v l) * M l j
        = ∑ l : K, star (v l * M j l) :=
          Finset.sum_congr rfl fun l _ => by rw [hcol l, star_mul']
      _ = star (∑ l : K, v l * M j l) := (star_sum _ _).symm
      _ = star (∑ l : K, M j l * v l) := by
          congr 1; exact Finset.sum_congr rfl fun l _ => mul_comm _ _
      _ = star ((M *ᵥ v) j) := by rw [mulVec_apply_sum]
      _ = star (v j) := by rw [h]
  calc ∑ l : K, v i * star (v l) * M l j
      = v i * ∑ l : K, star (v l) * M l j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = v i * star (v j) := by rw [hsum]

theorem colAt_injective (k0 : K) {v w : K → ℂ} (h : colAt k0 v = colAt k0 w) : v = w := by
  funext i
  have h2 := congrFun₂ h i k0
  rwa [colAt_apply, colAt_apply, if_pos rfl, if_pos rfl] at h2

/-- **Step A, the exact continuous-family shape the mapping-torus lane (`cc-lix-odd`) asked
for.**  `V` a continuous projection-valued map on `M`; `e`, `s` continuous unit vector fields
fixed by `V`; and a continuous field of partial isometries `w₁` implementing a Murray--von
Neumann equivalence, at every point, of the two complementary projections `V - e eᴴ` and
`V - s sᴴ`.  Conclusion: a continuous field of unitaries `g` of the corner determined by `V`,
with `g *ᵥ e = s`. -/
theorem exists_continuous_corner_unitary_apply_eq
    {M : Type*} [TopologicalSpace M] (k0 : K)
    {V : M → Matrix K K ℂ} {e s : M → K → ℂ}
    (hVproj : ∀ m, IsStarProjection (V m))
    (hVe : ∀ m, V m *ᵥ e m = e m) (hVs : ∀ m, V m *ᵥ s m = s m)
    (hecont : Continuous e) (hscont : Continuous s)
    (he1 : ∀ m, ∑ i, star (e m i) * e m i = 1) (hs1 : ∀ m, ∑ i, star (s m i) * s m i = 1)
    (w₁ : M → Matrix K K ℂ) (hw₁cont : Continuous w₁)
    (hw₁src : ∀ m, (w₁ m)ᴴ * w₁ m = V m - colAt k0 (e m) * (colAt k0 (e m))ᴴ)
    (hw₁rng : ∀ m, w₁ m * (w₁ m)ᴴ = V m - colAt k0 (s m) * (colAt k0 (s m))ᴴ)
    (hw₁pi : ∀ m, w₁ m * (w₁ m)ᴴ * w₁ m = w₁ m) :
    ∃ g : M → Matrix K K ℂ, Continuous g ∧
      (∀ m, g m * V m = g m) ∧ (∀ m, V m * g m = g m) ∧
      (∀ m, (g m)ᴴ * g m = V m) ∧ (∀ m, g m * (g m)ᴴ = V m) ∧
      (∀ m, g m *ᵥ e m = s m) := by
  have hmain : ∀ m : M,
      (colAt k0 (s m) * (colAt k0 (e m))ᴴ + w₁ m)ᴴ *
          (colAt k0 (s m) * (colAt k0 (e m))ᴴ + w₁ m) = V m ∧
        (colAt k0 (s m) * (colAt k0 (e m))ᴴ + w₁ m) *
          (colAt k0 (s m) * (colAt k0 (e m))ᴴ + w₁ m)ᴴ = V m ∧
        (colAt k0 (s m) * (colAt k0 (e m))ᴴ + w₁ m) * colAt k0 (e m) = colAt k0 (s m) :=
    fun m => mvn_complement_unitary_apply_eq (A := Matrix K K ℂ)
      (P := V m) (r := (colAt k0 (e m))ᴴ * colAt k0 (e m))
      (e := colAt k0 (e m)) (s := colAt k0 (s m)) (w₁ := w₁ m)
      (hVproj m).isSelfAdjoint.star_eq
      (colAt_pi_of_normSq_one (he1 m) k0) (colAt_pi_of_normSq_one (hs1 m) k0)
      rfl
      (colAt_conjTranspose_mul_colAt_eq_of_normSq_eq ((hs1 m).trans (he1 m).symm) k0)
      (mul_colAt_of_mulVec_eq (hVe m) k0) (mul_colAt_of_mulVec_eq (hVs m) k0)
      (colAt_mul_colAt_conjTranspose_mul_of_selfAdjoint_of_mulVec_eq
        (hVproj m).isSelfAdjoint.star_eq (hVs m) k0)
      (hw₁src m) (hw₁rng m) (hw₁pi m)
  refine ⟨fun m => colAt k0 (s m) * (colAt k0 (e m))ᴴ + w₁ m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((continuous_colAt k0 hscont).mul
      (continuous_colAt k0 hecont).matrix_conjTranspose).add hw₁cont
  · intro m
    exact GroupApproximation.LIX.mul_source_of_partialIsometry (hmain m).1
      ((hVproj m).isIdempotentElem.eq)
  · intro m
    have hq' : ((colAt k0 (s m) * (colAt k0 (e m))ᴴ + w₁ m)ᴴ)ᴴ *
        (colAt k0 (s m) * (colAt k0 (e m))ᴴ + w₁ m)ᴴ = V m := by
      rw [Matrix.conjTranspose_conjTranspose]; exact (hmain m).2.1
    have h2 := GroupApproximation.LIX.mul_source_of_partialIsometry hq'
      ((hVproj m).isIdempotentElem.eq)
    have h3 := congrArg Matrix.conjTranspose h2
    have hVstar : (V m)ᴴ = V m := (hVproj m).isSelfAdjoint.star_eq
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hVstar] at h3
  · exact fun m => (hmain m).1
  · exact fun m => (hmain m).2.1
  · intro m
    refine colAt_injective k0 ?_
    rw [← mul_colAt]
    exact (hmain m).2.2

end VectorForm

end STW59
end GroupApproximation
