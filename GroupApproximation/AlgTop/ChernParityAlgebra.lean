import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The pure-algebra core of the mapping-torus parity lemma

This file carries every step of the mapping-torus parity lemma (Lemma 3 of the
STW LIX manuscript) that is *algebra*: no bundles, no cohomology, no spaces.
The topological lanes supply the geometric inputs; what they get back from here
is an already-proved computation, so that the assembled lemma is a substitution
rather than a new proof.

The lemma to be assembled reads: for `M = S^5 × Y` with `Y = ∏_j CP^{d_j}`,
`V = 1^3 ⊕ H`, `r = m + 3`, and any complex rank-`r` bundle `W` over `S^1 × M`
restricting to `V` on the slice `{1} × M`, the top Chern number
`⟨c_r(W), [S^1 × M]⟩` is even.  Its proof has four algebraic joints.

## The four joints

1. **Newton with a square-zero Chern character.**  `δ = [W] - [p^*V]` has
   `ch(δ) = z ⬝ ch(β)` with `z = t x` a product of a degree-one and a
   degree-five generator, so `z ^ 2 = 0` and therefore `ch_i(δ) ch_j(δ) = 0`
   for all positive `i, j`.  Newton's identity then collapses to the *exact*
   formula `c_q(δ) = (-1)^(q-1) (q-1)! ch_q(δ)`, with no correction terms.
   This is `chern_eq_of_chernChar_sq_zero`.

2. **The line-monomial coefficient.**  For `β = ∏_j L_j^(a_j)` one has
   `ch(β) = exp(∑_j a_j h_j)`, so `ch_(n+3)(δ) = z g^n / n!` with
   `g = ∑_j a_j h_j`.  Feeding that through joint 1 gives
   `c_(n+3)(δ) = (-1)^n (n+2)(n+1) ⬝ z g^n`, which is **manifestly even**: the
   coefficient is a product of two consecutive integers and `z g^n` is an
   integral class.  This is `chern_of_expChar`, with the parity read off in
   `chern_of_expChar_even`.

   The manuscript instead expands `g^n` and records the coefficient of
   `z ∏_j h_j^(b_j)` as `(|b|+2)! / ∏_j b_j!`.  That number is an even natural
   number in complete generality: `even_factorial_div_prod_factorial`, proved
   from the exact factorisation `factorial_sum_add_two`.  The two routes agree,
   and the first needs no multinomial bookkeeping at all -- a genuine
   simplification of the written proof, recorded here as
   `factorial_div_prod_factorial_eq`.

3. **Whitney plus a degree count.**  `c(W) = c(p^*V) c(δ)` is a convolution.
   `c_r(p^*V) = 0` because `V` is pulled back from a space of dimension
   `2m < 2r`, and every surviving term carries a positive Chern class of `δ`.
   This is `dvd_of_convolution_top`.

4. **Rational computation, integral conclusion.**  The cohomology of
   `S^1 × S^5 × Y` is torsion free, so the divisibility proved over `ℚ`
   descends to `ℤ`: `dvd_of_map_eq_mul`.

## Scope

Nothing here mentions a topological space, so the whole file is unconditional
Mathlib-only algebra.  The `ℚ`-algebra hypothesis in joints 1 and 2 is the
rational cohomology ring; it is used only to divide by the positive integer
`q` that Newton's identity leaves in front of `c q`, and joint 4 is what turns
the rational conclusion back into an integral one.
-/

namespace GroupApproximation
namespace ChernParityAlgebra

open Finset
open scoped Nat

/-! ## Consecutive integers and multinomial coefficients -/

section Multinomial

variable {ι : Type*}

/-- One of two consecutive integers is even. -/
theorem even_add_two_mul_add_one (m : ℕ) : Even ((m + 2) * (m + 1)) := by
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨(j + 1) * (m + 1), by subst hj; ring⟩
  · exact ⟨(m + 2) * (j + 1), by subst hj; ring⟩

/-- The exact factorisation behind the manuscript's coefficient
`(|b| + 2)! / ∏ b_j !`: writing `n = ∑ b i`, one has
`(n + 2)! = (∏ (b i)!) ⬝ (n + 2)(n + 1) ⬝ multinomial b`. -/
theorem factorial_sum_add_two (s : Finset ι) (b : ι → ℕ) :
    ((∑ i ∈ s, b i) + 2)! =
      (∏ i ∈ s, (b i)!) *
        (((∑ i ∈ s, b i) + 2) * ((∑ i ∈ s, b i) + 1) * Nat.multinomial s b) := by
  have hstep : ∀ m : ℕ, (m + 2)! = (m + 2) * ((m + 1) * m !) := by
    intro m
    have h1 : (m + 2)! = (m + 2) * (m + 1)! := Nat.factorial_succ (m + 1)
    have h2 : (m + 1)! = (m + 1) * m ! := Nat.factorial_succ m
    rw [h1, h2]
  have hspec := Nat.multinomial_spec s b
  rw [hstep (∑ i ∈ s, b i), ← hspec]
  ring

/-- The manuscript's coefficient is an integer: `∏ (b i)!` divides
`(∑ b + 2)!`, with explicit quotient `(∑ b + 2)(∑ b + 1) ⬝ multinomial b`. -/
theorem factorial_div_prod_factorial_eq (s : Finset ι) (b : ι → ℕ) :
    ((∑ i ∈ s, b i) + 2)! / (∏ i ∈ s, (b i)!)
      = ((∑ i ∈ s, b i) + 2) * ((∑ i ∈ s, b i) + 1) * Nat.multinomial s b := by
  rw [factorial_sum_add_two, Nat.mul_div_cancel_left _ (Nat.prod_factorial_pos s b)]

/-- **Equation (2.8) of the manuscript.**  The coefficient
`(|b| + 2)! / ∏ b_j !` is an even natural number, for every finite multi-index
`b`.  This is the arithmetic heart of the parity lemma, and it holds in
complete generality: the quotient is `(|b| + 2)(|b| + 1)` times a multinomial
coefficient, and a product of two consecutive integers is even. -/
theorem even_factorial_div_prod_factorial (s : Finset ι) (b : ι → ℕ) :
    Even (((∑ i ∈ s, b i) + 2)! / ∏ i ∈ s, (b i)!) := by
  rw [factorial_div_prod_factorial_eq]
  exact (even_add_two_mul_add_one _).mul_right _

/-- The division-free form of `even_factorial_div_prod_factorial`. -/
theorem two_mul_prod_factorial_dvd_factorial (s : Finset ι) (b : ι → ℕ) :
    2 * ∏ i ∈ s, (b i)! ∣ ((∑ i ∈ s, b i) + 2)! := by
  obtain ⟨k, hk⟩ := even_add_two_mul_add_one (∑ i ∈ s, b i)
  refine ⟨k * Nat.multinomial s b, ?_⟩
  rw [factorial_sum_add_two, hk]
  ring

end Multinomial

/-! ## Newton's identity with a square-zero Chern character -/

section Newton

variable {R : Type*} [CommRing R]

/-- Newton's identity relating the Chern classes `c q` of a (virtual) bundle to
the components `ch q` of its Chern character.

With Chern roots `x 1, …, x N`, the classical identity between elementary
symmetric functions `e q` and power sums `p q` reads
`∑_(i < q) (-1)^i e_i p_(q-i) + (-1)^q q e_q = 0`; substituting `e_q = c_q` and
`p_q = q ! ⬝ ch_q` gives exactly the field `newton` below.  It is a hypothesis
rather than a derivation here because deriving it is the splitting principle,
and therefore topology; `found-chern-classes` owns that step. -/
structure NewtonIdentity (c ch : ℕ → R) : Prop where
  /-- The total Chern class starts at `1`. -/
  chern_zero : c 0 = 1
  /-- Newton's identity in every positive degree. -/
  newton : ∀ q : ℕ, 0 < q →
    (∑ i ∈ Finset.range q,
        (-1 : R) ^ i * c i * (((q - i)! : ℕ) : R) * ch (q - i))
      + (-1 : R) ^ q * (q : R) * c q = 0

variable [Algebra ℚ R]

/-- A nonzero natural number is a unit in any `ℚ`-algebra.  This is the only
use made of the rational coefficients: Newton's identity determines `q ⬝ c q`,
and `q` has to be divided out. -/
theorem isUnit_natCast_of_ne_zero {n : ℕ} (hn : n ≠ 0) : IsUnit ((n : ℕ) : R) := by
  have h1 : ((n : ℕ) : ℚ) ≠ 0 := by simpa using hn
  have h2 := IsUnit.map (algebraMap ℚ R) (isUnit_iff_ne_zero.mpr h1)
  rwa [map_natCast] at h2

/-- **Equation (2.7) of the manuscript.**  If every product of two
positive-degree components of the Chern character vanishes -- which happens in
the parity lemma because each of them is divisible by a class `z` with
`z ^ 2 = 0` -- then Newton's identity collapses to the exact formula
`c q = (-1)^(q-1) (q-1)! ⬝ ch q`.

No `log`/`exp` machinery is needed.  The hypothesis kills every cross term of
the Newton recursion except the leading one, and a single strong induction is
what is left. -/
theorem chern_eq_of_chernChar_sq_zero {c ch : ℕ → R}
    (hN : NewtonIdentity c ch)
    (hsq : ∀ i j : ℕ, 0 < i → 0 < j → ch i * ch j = 0) :
    ∀ q : ℕ, 0 < q → c q = (-1 : R) ^ (q - 1) * ((((q - 1)! : ℕ)) : R) * ch q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq
    have hnewton := hN.newton q hq
    have hzero : ∀ i ∈ Finset.range q, i ≠ 0 →
        (-1 : R) ^ i * c i * (((q - i)! : ℕ) : R) * ch (q - i) = 0 := by
      intro i hi hi0
      have hiq : i < q := Finset.mem_range.mp hi
      have hipos : 0 < i := by omega
      have hsub : 0 < q - i := by omega
      have hz : ch i * ch (q - i) = 0 := hsq i (q - i) hipos hsub
      rw [ih i hiq hipos]
      have hrw :
          (-1 : R) ^ i * ((-1 : R) ^ (i - 1) * ((((i - 1)! : ℕ)) : R) * ch i) *
              (((q - i)! : ℕ) : R) * ch (q - i)
            = ((-1 : R) ^ i * (-1 : R) ^ (i - 1) * ((((i - 1)! : ℕ)) : R) *
              (((q - i)! : ℕ) : R)) * (ch i * ch (q - i)) := by ring
      rw [hrw, hz, mul_zero]
    have hsum :
        (∑ i ∈ Finset.range q,
            (-1 : R) ^ i * c i * (((q - i)! : ℕ) : R) * ch (q - i))
          = (((q ! : ℕ)) : R) * ch q := by
      refine (Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hq) hzero).trans ?_
      rw [hN.chern_zero]
      simp
    rw [hsum] at hnewton
    obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hfac : (((n + 1)! : ℕ) : R) = ((n + 1 : ℕ) : R) * ((n ! : ℕ) : R) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    have hpow : (-1 : R) ^ (n + 1) = -((-1 : R) ^ n) := by
      rw [pow_succ]; ring
    have hs : ((-1 : R) ^ n) * ((-1 : R) ^ n) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨n, rfl⟩
    rw [hfac, hpow] at hnewton
    refine (isUnit_natCast_of_ne_zero (R := R) (n := n + 1) (by omega)).mul_left_cancel ?_
    linear_combination (-((-1 : R) ^ n)) * hnewton
      + (-(((n + 1 : ℕ) : R) * c (n + 1))) * hs

/-- The Chern character of a virtual class of the shape `z ⬝ exp g` with
`z * z = 0` has all its positive-degree products zero.  `hlow` records that
`ch` starts in degree three (the class `z = t x` sits in `H^6`, and `δ` has
rank zero); `hhigh` is the integral normalisation `n ! ⬝ ch_(n+3) = z g^n`,
stated without division because that is the form the Chern character actually
delivers. -/
theorem chernChar_sq_zero_of_expChar {ch : ℕ → R} {z g : R} (hz : z * z = 0)
    (hlow : ∀ q : ℕ, q < 3 → ch q = 0)
    (hhigh : ∀ n : ℕ, ((n ! : ℕ) : R) * ch (n + 3) = z * g ^ n) :
    ∀ i j : ℕ, 0 < i → 0 < j → ch i * ch j = 0 := by
  intro i j _ _
  rcases Nat.lt_or_ge i 3 with hi | hi
  · rw [hlow i hi, zero_mul]
  rcases Nat.lt_or_ge j 3 with hj | hj
  · rw [hlow j hj, mul_zero]
  obtain ⟨a, rfl⟩ : ∃ a, i = a + 3 := ⟨i - 3, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, j = b + 3 := ⟨j - 3, by omega⟩
  have hkey : ((a ! : ℕ) : R) * ch (a + 3) * (((b ! : ℕ) : R) * ch (b + 3)) = 0 := by
    rw [hhigh a, hhigh b]
    have hcomm : z * g ^ a * (z * g ^ b) = (z * z) * (g ^ a * g ^ b) := by ring
    rw [hcomm, hz, zero_mul]
  have hu : IsUnit (((a ! * b ! : ℕ)) : R) :=
    isUnit_natCast_of_ne_zero (R := R)
      (Nat.mul_ne_zero (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b))
  refine hu.mul_left_cancel ?_
  rw [Nat.cast_mul, mul_zero]
  linear_combination hkey

/-- **The parity computation, joint 2.**  For a virtual class with Chern
character `z ⬝ exp g` and `z * z = 0`, the Chern classes are given exactly by
`c_(n+3) = (-1)^n (n+2)(n+1) ⬝ z g^n`.

The coefficient is `(n+2)! / n!`, a product of two consecutive integers, which
is where the parity comes from.  The manuscript reaches the same conclusion by
expanding `g^n` into line monomials and computing `(|b|+2)! / ∏ b_j !`; that
expansion is `even_factorial_div_prod_factorial` above and is not needed
here. -/
theorem chern_of_expChar {c ch : ℕ → R} {z g : R}
    (hN : NewtonIdentity c ch) (hz : z * z = 0)
    (hlow : ∀ q : ℕ, q < 3 → ch q = 0)
    (hhigh : ∀ n : ℕ, ((n ! : ℕ) : R) * ch (n + 3) = z * g ^ n) :
    ∀ n : ℕ,
      c (n + 3) = (-1 : R) ^ n * ((((n + 2) * (n + 1) : ℕ)) : R) * (z * g ^ n) := by
  intro n
  have hsq := chernChar_sq_zero_of_expChar hz hlow hhigh
  have hmain := chern_eq_of_chernChar_sq_zero hN hsq (n + 3) (by omega)
  have hidx : n + 3 - 1 = n + 2 := by omega
  rw [hidx] at hmain
  have hsign : (-1 : R) ^ (n + 2) = (-1 : R) ^ n := by
    rw [pow_add]
    have hsq2 : (-1 : R) ^ 2 = 1 := by ring
    rw [hsq2, mul_one]
  have hfac : (((n + 2)! : ℕ) : R)
      = ((((n + 2) * (n + 1) : ℕ)) : R) * ((n ! : ℕ) : R) := by
    have h1 : (n + 2)! = ((n + 2) * (n + 1)) * n ! := by
      have e1 : (n + 2)! = (n + 2) * (n + 1)! := Nat.factorial_succ (n + 1)
      have e2 : (n + 1)! = (n + 1) * n ! := Nat.factorial_succ n
      rw [e1, e2]; ring
    rw [h1, Nat.cast_mul]
  rw [hmain, hsign, hfac]
  have hcollapse :
      (-1 : R) ^ n * (((((n + 2) * (n + 1) : ℕ)) : R) * ((n ! : ℕ) : R)) * ch (n + 3)
        = (-1 : R) ^ n * ((((n + 2) * (n + 1) : ℕ)) : R) *
            (((n ! : ℕ) : R) * ch (n + 3)) := by ring
  rw [hcollapse, hhigh n]

/-- The parity statement of joint 2: every positive Chern class of a virtual
class with Chern character `z ⬝ exp g`, `z * z = 0`, is twice an explicit
integral combination of the classes `z g^n`. -/
theorem chern_of_expChar_even {c ch : ℕ → R} {z g : R}
    (hN : NewtonIdentity c ch) (hz : z * z = 0)
    (hlow : ∀ q : ℕ, q < 3 → ch q = 0)
    (hhigh : ∀ n : ℕ, ((n ! : ℕ) : R) * ch (n + 3) = z * g ^ n) (n : ℕ) :
    ∃ k : ℕ, c (n + 3) = 2 * ((-1 : R) ^ n * (k : R) * (z * g ^ n)) := by
  obtain ⟨k, hk⟩ := even_add_two_mul_add_one n
  refine ⟨k, ?_⟩
  rw [chern_of_expChar hN hz hlow hhigh n, hk]
  push_cast
  ring

/-- Below degree three these Chern classes vanish outright: the manuscript's
"there are no terms for `q < 3`". -/
theorem chern_of_expChar_low {c ch : ℕ → R} {z g : R}
    (hN : NewtonIdentity c ch) (hz : z * z = 0)
    (hlow : ∀ q : ℕ, q < 3 → ch q = 0)
    (hhigh : ∀ n : ℕ, ((n ! : ℕ) : R) * ch (n + 3) = z * g ^ n) :
    ∀ q : ℕ, 0 < q → q < 3 → c q = 0 := by
  intro q hq hq3
  have hsq := chernChar_sq_zero_of_expChar hz hlow hhigh
  rw [chern_eq_of_chernChar_sq_zero hN hsq q hq, hlow q hq3, mul_zero]

/-- Both halves of joint 2 in the single form the assembly consumes: every
Chern class of `δ` in positive degree is divisible by `2`. -/
theorem two_dvd_chern_of_expChar {c ch : ℕ → R} {z g : R}
    (hN : NewtonIdentity c ch) (hz : z * z = 0)
    (hlow : ∀ q : ℕ, q < 3 → ch q = 0)
    (hhigh : ∀ n : ℕ, ((n ! : ℕ) : R) * ch (n + 3) = z * g ^ n) :
    ∀ q : ℕ, 0 < q → (2 : R) ∣ c q := by
  intro q hq
  rcases Nat.lt_or_ge q 3 with hq3 | hq3
  · rw [chern_of_expChar_low hN hz hlow hhigh q hq hq3]
    exact dvd_zero 2
  · obtain ⟨n, rfl⟩ : ∃ n, q = n + 3 := ⟨q - 3, by omega⟩
    obtain ⟨k, hk⟩ := chern_of_expChar_even hN hz hlow hhigh n
    exact ⟨_, hk⟩

end Newton

/-! ## Whitney's formula and the degree count -/

section Whitney

variable {R : Type*} [CommRing R]

/-- **The last step of the manuscript's proof.**  The total Chern class of `W`
is the convolution of those of `p^*V` and of `δ`.  The one term of the top
component `r` that carries `c_0(δ) = 1` also carries `c_r(p^*V)`, which
vanishes for dimension reasons; every other term carries a positive Chern class
of `δ`, all of which are divisible by `d`.  So `d` divides `c_r(W)`. -/
theorem dvd_of_convolution_top {u v w : ℕ → R} {r : ℕ} {d : R}
    (hw : w r = ∑ p ∈ Finset.antidiagonal r, u p.1 * v p.2)
    (hu : u r = 0) (hv : ∀ j : ℕ, 0 < j → d ∣ v j) : d ∣ w r := by
  rw [hw]
  refine Finset.dvd_sum ?_
  intro p hp
  by_cases h0 : p.2 = 0
  · have hpr : p.1 = r := by
      have hsum := Finset.mem_antidiagonal.mp hp
      omega
    rw [hpr, hu, zero_mul]
    exact dvd_zero d
  · exact dvd_mul_of_dvd_right (hv p.2 (by omega)) _

end Whitney

/-! ## From a rational computation to an integral one -/

section Integrality

/-- Joint 4.  The cohomology of `S^1 × S^5 × Y` is torsion free, so an integral
class whose image in rational cohomology is `2` times another integral class is
itself `2` times an integral class.  Stated for an arbitrary injective ring
map, which is the only property of the coefficient inclusion that is used. -/
theorem dvd_of_map_eq_mul {S R : Type*} [CommRing S] [CommRing R] (f : S →+* R)
    (hf : Function.Injective f) {d x w : S} (h : f x = f d * f w) : d ∣ x :=
  ⟨w, hf (by rw [h, map_mul])⟩

end Integrality

end ChernParityAlgebra
end GroupApproximation
