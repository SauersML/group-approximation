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
symmetric function of the roots **with no sign**; this is also the convention that
makes `γ(L) = X + e(L)` for a line bundle.

**1. The choice is free, and it used not to look free.**  This file's docstring
used to say that over `ZMod 2` signs are invisible anyway.  That was **true**, and
it was true because of two choices that have both since changed: the tree took the
class of the projective bundle to be `e(taut)`, whose roots are `y = −a` for the
honest Chern roots `a`, and it worked only over `F₂`, where nothing distinguishes
`y` from `a`.  Neither is forced.  Take instead `ξ = e(O(1))`, the Euler class of
the **dual** of the tautological line, which is the class the classical statement
uses.  Then `c_r(π^*E ⊗ O(1)) = ∏ (ξ + a_i) = 0` over **any** ring, with the honest
Chern roots and `+` signs: on the locus where the tautological line is the `i`-th
summand `O(1) = L_i⁻¹`, so the factor is `−a_i + a_i` and dies by
`neg_add_cancel`, where the mod-2 proof killed `a_i + a_i` by `add_self`.

**So the `y_l` of `∏ (X + y_l)` above ARE the classical Chern roots, and
`γ_k = e_k(y) = c_k` with no sign at all.**  That is the lead's ruling of
2026-09-10 15:50, `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5, "Ruling on the
roots"; it is stated there and pointed at here, and it is not to be restated
anywhere else.  The morning's formulation — that the roots are the negatives of the
usual ones — is **retired**: it described the old relation, the one written with
`e(taut)`.  The deleted `ZMod 2` sentence was likewise not wrong, it was about a
tree that made two other choices.

**2. This file fixes the convention, and nothing else may.**  The splitting
principle, the Chern layer and the even side all point at this paragraph instead of
restating it.  Restating it is how the next lane to touch one of the three restates
it differently, and the mismatch then surfaces as a sign in a Wu relation, which is
the hardest place to find one.

**3. Moving between the two conventions is `φ : h ↦ −h`, and that is a licence,
not a curiosity** (`sp-design`, third pass).  The two conventions differ by exactly
the ring automorphism `φ` of `H^*(Y)`, which exists because `H^*(∏ ℂP^{d_i})` is
generated in degree two: `φ(c_j) = e_j(−a) = (−1)^j e_j(a)`.  That `φ` commutes
with the total reduced power `P` rests on exactly **two sign identities in `F_p`**:

```text
(-1)^p = -1        and        (-1)^(i * (p-1)) = 1
```

Each holds at **every** prime, and this is the checkable form of the claim rather
than an atmospheric one.

**There are exactly two because there are two levels, and each has its own sign to
clear.**  `φ` acts on a weight-`w` homogeneous element by `(−1)^w`, one sign per
generator.  Then:

* `(−1)^p = −1` is what makes `φ` commute with the **total** `P` on the degree-two
  generators: `P(φh) = −h − h^p` against `φ(Ph) = −h + (−h)^p`, and equality is
  exactly that identity.  It extends to everything else because `P` and `φ` are
  both ring maps.
* `(−1)^{i(p−1)} = 1` is what makes `φ` commute with each **graded piece** `P^i`:
  on weight `w`, `P^i(φx) = (−1)^w P^i x` while `φ(P^i x) = (−1)^{w + i(p−1)} P^i x`.
  This is the same computation that makes every weight component of `E_j` scale by
  the same `(−1)^j`, so it is the identity the **Wu covariance actually consumes**.

Do not delete the second as redundant.  A reader who meets two identities with one
job between them will suspect one is spare, and the one they will drop is the
second — which is the one the even side uses.

Each identity holds for **two different reasons**, and neither reason is an
instance of the other:

* at odd `p`, because the relevant exponent is even — `p` is odd in the first
  identity, `p − 1` is even in the second — so every weight component of `E_j`
  scales by the same `(−1)^j` and the Wu relations, the Frobenius step and the
  conclusion are all covariant, so anything proved in one convention transfers to
  the other term by term;
* at `p = 2`, because `−1 = 1` in `F₂`.  Equivalently and more usefully, `φ` is
  there the **identity**, so the `F₂` layer does not see the change at all and
  stays green without re-proof — which is why the switch is safe to make now rather
  than after the `F₂` surface is retired.

At `p = 2` the odd-`p` reason does **not** apply, since `p − 1` is odd there; `φ`
commutes with `P` for the other reason.  A reader who keeps only the uniform
identity, without both reasons, has a sentence one step away from "signs are
invisible over `ZMod 2`" — the sentence this paragraph exists to have deleted.

*Provenance, because it is the argument for recording both halves, and because the
two halves were found by different **methods** rather than merely by different
people — which tells the next reader which method to reach for at the next sign.*
`sp-coeff` reached the identity **symbolically**, did not see that it needs two
reasons, and had one of the two wrong: the check was performed in `ℤ`, where the
two sides genuinely disagree at `p = 2`, rather than in `F_p`, where the classes
live and where they agree.  `sp-design` reached the two reasons from the **failure
of the odd-`p` justification** at `p = 2` — the argument fails there, not the
conclusion — and did not see that the identities are uniform.  Neither had it
whole, and the useful output was the disagreement rather than either reading.

A check performed in the wrong setting reads exactly like a check.  That one erred
toward extra caution, which is the kind nobody pushes back on.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open Polynomial

section Relation

-- `B` needs only `Ring`: `PowerBasis` and `aeval` do, and requiring `CommRing` here would
-- force a `CommSemiring` on the total space of a projective bundle, which is exactly the
-- graded-ring instance that is not available until `cup_comm` lands.  Commutativity of `B`
-- is needed only in `section Split`, where a `Finset.prod` is taken in `B`.
variable {A B : Type*} [CommRing A] [Ring B] [Algebra A B]

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

variable {A A' B B' : Type*} [CommRing A] [Ring B] [Algebra A B]
variable [CommRing A'] [Ring B'] [Algebra A' B']

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

variable {A A' : Type*} [CommRing A] [CommRing A']

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
