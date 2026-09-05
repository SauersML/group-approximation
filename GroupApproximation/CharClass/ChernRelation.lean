import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The defining relation of the mod-2 Chern classes, as pure algebra

Grothendieck's definition of the Chern classes of a rank-`r` bundle `E → X` reads

```text
ξ^r + γ₁(E) ξ^{r-1} + ⋯ + γ_r(E) = 0    in H^*(P(E)),
```

where `ξ` is the class of the tautological line on the projective bundle and
Leray–Hirsch says that `1, ξ, …, ξ^{r-1}` is a **basis** of `H^*(P(E))` as a
module over `H^*(X)`.  This file isolates *exactly* that algebra, with no
topology in it at all: the Leray–Hirsch conclusion is the statement that a
commutative `A`-algebra `B` carries a `Mathlib` `PowerBasis A B`, and the
Chern polynomial is then the associated `minpolyGen`.

Everything downstream about `γ` — that `γ₀ = 1`, that `γ_k` vanishes above the
rank, naturality under base change, the split form `γ_k = e_k(y₁, …, y_r)`, and
the Whitney sum formula transported along an injective base change — is a
statement about `Polynomial A` and is proved here once and for all.

## Main declarations

* `chernPoly pb` — the monic degree-`pb.dim` polynomial killing `pb.gen`.
* `chernPoly_eq_of_monic` — **uniqueness**: any monic polynomial of degree
  `pb.dim` killing `pb.gen` *is* `chernPoly pb`.  This is the workhorse: every
  identity below is proved by exhibiting a monic polynomial of the right degree
  that kills the generator.
* `chernClass pb k` — the `k`-th coefficient, `γ_k`.
* `chernClass_zero`, `chernClass_eq_zero_of_lt` — normalization and the rank bound.
* `chernPoly_map` — naturality under a base change that preserves the relation.
* `chernPoly_eq_prod_of_root` and `chernClass_eq_esymm` — the split case.
* `chernPoly_mul_of_map_injective` — the Whitney sum formula, reduced to the
  split case along an injective base change (the splitting principle).

## Conventions

The relation is written with `+` signs, `p = X^r + γ₁ X^{r-1} + ⋯ + γ_r`, so
that in the split case `p = ∏ (X + y_k)` and `γ_k` is the `k`-th elementary
symmetric function of the roots **with no sign**.  Over `ZMod 2` — the only
coefficient ring this project ever uses — signs are invisible anyway, and this
convention is the one that makes `γ(L) = X + e(L)` for a line bundle.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open Polynomial

section Relation

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The **Chern polynomial** of a Leray–Hirsch presentation `pb : PowerBasis A B`:
the monic polynomial `X^r + γ₁ X^{r-1} + ⋯ + γ_r` of degree `r = pb.dim` that
annihilates the tautological class `pb.gen`. -/
noncomputable def chernPoly (pb : PowerBasis A B) : A[X] := pb.minpolyGen

theorem chernPoly_monic (pb : PowerBasis A B) : (chernPoly pb).Monic :=
  pb.minpolyGen_monic

/-- **The defining relation.** `ξ^r + γ₁ ξ^{r-1} + ⋯ + γ_r = 0`. -/
theorem aeval_gen_chernPoly (pb : PowerBasis A B) :
    aeval pb.gen (chernPoly pb) = 0 :=
  pb.aeval_minpolyGen

theorem degree_chernPoly [Nontrivial A] (pb : PowerBasis A B) :
    (chernPoly pb).degree = (pb.dim : WithBot ℕ) :=
  pb.degree_minpolyGen

theorem natDegree_chernPoly [Nontrivial A] (pb : PowerBasis A B) :
    (chernPoly pb).natDegree = pb.dim :=
  pb.natDegree_minpolyGen

/-- **Uniqueness of the Chern polynomial.**  A monic polynomial of degree exactly
`pb.dim` that annihilates the generator is the Chern polynomial.  Every structural
identity for `γ` below is an instance of this lemma. -/
theorem chernPoly_eq_of_monic [Nontrivial A] (pb : PowerBasis A B) {p : A[X]}
    (hp : p.Monic) (hdeg : p.natDegree = pb.dim) (hroot : aeval pb.gen p = 0) :
    p = chernPoly pb := by
  by_contra hne
  have hp0 : p ≠ 0 := hp.ne_zero
  have hdegp : p.degree = (pb.dim : WithBot ℕ) := by
    rw [degree_eq_natDegree hp0, hdeg]
  have hsub : p - chernPoly pb ≠ 0 := sub_ne_zero.mpr hne
  have hlt : (p - chernPoly pb).degree < p.degree :=
    degree_sub_lt (by rw [hdegp, degree_chernPoly]) hp0
      (by rw [hp.leadingCoeff, (chernPoly_monic pb).leadingCoeff])
  have hroot' : aeval pb.gen (p - chernPoly pb) = 0 := by
    rw [map_sub, hroot, aeval_gen_chernPoly, sub_zero]
  have hge : (pb.dim : WithBot ℕ) ≤ (p - chernPoly pb).degree :=
    pb.dim_le_degree_of_root hsub hroot'
  rw [hdegp] at hlt
  exact absurd (lt_of_le_of_lt hge hlt) (lt_irrefl _)

/-- The `k`-th **mod-2 Chern class** of a Leray–Hirsch presentation: the
coefficient of `X^{r-k}` in the Chern polynomial, and `0` above the rank. -/
noncomputable def chernClass (pb : PowerBasis A B) (k : ℕ) : A :=
  if k ≤ pb.dim then (chernPoly pb).coeff (pb.dim - k) else 0

theorem chernClass_of_le (pb : PowerBasis A B) {k : ℕ} (hk : k ≤ pb.dim) :
    chernClass pb k = (chernPoly pb).coeff (pb.dim - k) :=
  if_pos hk

/-- **Rank bound.** `γ_k = 0` for `k` above the rank. -/
theorem chernClass_eq_zero_of_lt (pb : PowerBasis A B) {k : ℕ} (hk : pb.dim < k) :
    chernClass pb k = 0 :=
  if_neg (by omega)

/-- **Normalization.** `γ₀ = 1`. -/
@[simp]
theorem chernClass_zero [Nontrivial A] (pb : PowerBasis A B) : chernClass pb 0 = 1 := by
  rw [chernClass_of_le pb (Nat.zero_le _), Nat.sub_zero]
  simpa [Polynomial.leadingCoeff, natDegree_chernPoly] using (chernPoly_monic pb).leadingCoeff

/-- The Chern polynomial, written out from its classes:
`X^r + γ₁ X^{r-1} + ⋯ + γ_r = ∑_{k ≤ r} γ_k X^{r-k}`. -/
theorem chernPoly_eq_sum [Nontrivial A] (pb : PowerBasis A B) :
    chernPoly pb = ∑ k ∈ Finset.range (pb.dim + 1), C (chernClass pb k) * X ^ (pb.dim - k) := by
  ext n
  rw [finsetSum_coeff]
  by_cases hn : n ≤ pb.dim
  · rw [Finset.sum_eq_single (pb.dim - n)]
    · rw [coeff_C_mul, coeff_X_pow, if_pos (by omega),
        chernClass_of_le pb (by omega), mul_one]
      congr 1
      omega
    · intro b hb hbn
      rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
      simp only [Finset.mem_range] at hb
      omega
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · have hzero : (chernPoly pb).coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [natDegree_chernPoly]; omega)
    rw [hzero, Finset.sum_eq_zero]
    intro b hb
    simp only [Finset.mem_range] at hb
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

end Relation

section Naturality

variable {A A' B B' : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [CommRing A'] [CommRing B'] [Algebra A' B']

/-- **Naturality.**  If a ring map `f : A → A'` carries the Chern relation of `pb`
to a relation satisfied by the generator of `pb'`, and the two ranks agree, then
the Chern polynomial of `pb'` is the image of that of `pb`.

Topologically: for `g : X' → X` the projective bundle of `g^* E` is the pullback
of `P(E)`, the tautological class pulls back to the tautological class, so the
pulled-back relation still holds and uniqueness identifies the two polynomials. -/
theorem chernPoly_map [Nontrivial A] [Nontrivial A'] (pb : PowerBasis A B)
    (pb' : PowerBasis A' B') (f : A →+* A') (hdim : pb'.dim = pb.dim)
    (hroot : aeval pb'.gen ((chernPoly pb).map f) = 0) :
    chernPoly pb' = (chernPoly pb).map f := by
  refine (chernPoly_eq_of_monic pb' ((chernPoly_monic pb).map f) ?_ hroot).symm
  rw [(chernPoly_monic pb).natDegree_map, hdim, natDegree_chernPoly]

/-- **Naturality in coefficients.** -/
theorem chernClass_map [Nontrivial A] [Nontrivial A'] (pb : PowerBasis A B)
    (pb' : PowerBasis A' B') (f : A →+* A') (hdim : pb'.dim = pb.dim)
    (hroot : aeval pb'.gen ((chernPoly pb).map f) = 0) (k : ℕ) :
    chernClass pb' k = f (chernClass pb k) := by
  unfold chernClass
  rw [chernPoly_map pb pb' f hdim hroot, hdim]
  by_cases hk : k ≤ pb.dim
  · rw [if_pos hk, if_pos hk, coeff_map]
  · rw [if_neg hk, if_neg hk, map_zero]

end Naturality

section Split

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- **The split case.**  If the generator satisfies `∏_{i ∈ s} (ξ + y_i) = 0` with
`s` of cardinality the rank, then the Chern polynomial is `∏_{i ∈ s} (X + y_i)`:
the `y_i` are the Chern roots. -/
theorem chernPoly_eq_prod_of_root [Nontrivial A] {ι : Type*} (pb : PowerBasis A B)
    (s : Finset ι) (y : ι → A) (hcard : s.card = pb.dim)
    (hroot : ∏ i ∈ s, (pb.gen + algebraMap A B (y i)) = 0) :
    chernPoly pb = ∏ i ∈ s, (X + C (y i)) := by
  refine (chernPoly_eq_of_monic pb ?_ ?_ ?_).symm
  · exact monic_prod_of_monic _ _ fun i _ => monic_X_add_C (y i)
  · rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_add_C (y i)]
    simp only [natDegree_X_add_C]
    rw [Finset.sum_const, smul_eq_mul, mul_one, hcard]
  · rw [map_prod]
    simpa only [map_add, aeval_X, aeval_C] using hroot

/-- **The split case in coefficients**: `γ_k = e_k(y₁, …, y_r)`, the `k`-th
elementary symmetric function of the Chern roots. -/
theorem chernClass_eq_esymm [Nontrivial A] {ι : Type*} (pb : PowerBasis A B)
    (s : Finset ι) (y : ι → A) (hcard : s.card = pb.dim)
    (hroot : ∏ i ∈ s, (pb.gen + algebraMap A B (y i)) = 0) {k : ℕ} (hk : k ≤ pb.dim) :
    chernClass pb k = ∑ t ∈ s.powersetCard k, ∏ i ∈ t, y i := by
  rw [chernClass_of_le pb hk, chernPoly_eq_prod_of_root pb s y hcard hroot,
    Finset.prod_X_add_C_coeff s y (by omega)]
  congr 2
  omega

end Split

section Whitney

variable {A A' B B' : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [CommRing A'] [CommRing B'] [Algebra A' B']

/-- **The Whitney sum formula, reduced to the splitting principle.**

If an injective base change `f : A → A'` — topologically, the pullback to the
flag bundle, injective by Leray–Hirsch — carries the three Chern polynomials of
`E`, `E'` and `E ⊕ E'` to polynomials whose product identity is already known
(because everything splits into lines upstairs), then the identity holds
downstairs.  Together with `chernPoly_eq_prod_of_root` this is the whole content
of `γ(E ⊕ E') = γ(E) γ(E')`. -/
theorem chernPoly_mul_of_map_injective {f : A →+* A'} (hf : Function.Injective f)
    {p q r : A[X]}
    (h : r.map f = p.map f * q.map f) : r = p * q :=
  Polynomial.map_injective f hf (by rw [h, Polynomial.map_mul])

/-- The coefficient form of the Whitney sum formula: from `r = p * q` on
polynomials, the coefficients convolve. -/
theorem coeff_mul_chern {p q : A[X]} {m n : ℕ} :
    (p * q).coeff (m + n) = ∑ x ∈ Finset.antidiagonal (m + n), p.coeff x.1 * q.coeff x.2 :=
  Polynomial.coeff_mul p q (m + n)

end Whitney

end CharClass
end GroupApproximation
