import GroupApproximation.AlgTop.MappingTorusParity

/-!
# The closing contradiction of Lemma 2

Lane `lix-obstruction`, campaign target 3 (STW Problem LIX).

Manuscript
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`,
proof of Lemma 2, ends by putting two computations of the same integer against
each other:

* the section (2.10) of the mapping-torus bundle `W_g` has isolated transverse
  zeros whose signed total is `±1`, so `⟨c_r(W_g), [S¹ × M]⟩ = ±1`;
* Lemma 3 says that same integer is **even**.

This file is that last step, and nothing else.  It exists so that the seam
between `found-euler-class`'s zero count and `found-mapping-torus-parity`'s
parity is a named theorem rather than a line of prose, and so that the two
shapes are checked against each other **now**, while reshaping either is cheap.

`found-mapping-torus-parity` supplies
`AlgTop.MappingTorusParity.even_chernClass_top_pairing_of_sumLine`, which is
Lemma 3 with `hV` already discharged from the manuscript's
`V = 1³ ⊕ H`, `H = ⨁_j L_j^{⊕ d_j}`: one passes the presentation
`V = ∏_a (line (h a)) ^ (d a)` and the rank bound `∑_a d a < r`.  For the
manuscript that bound is `m < m + 3`, so it is immediate and, in particular,
**no dimension count `dim Y = 2m < 2r` is needed anywhere** — `c_r(V) = 0` is a
statement about the rank of `V`, true over any base.

## Main results

* `false_of_parity_of_odd_pairing` — the contradiction from an **odd** pairing.
* `false_of_parity_of_pairing_eq_one` — the same from the manuscript's `±1`.

## What is deliberately not here

No bundle, no mapping torus, no section, no manifold.  `S` is any commutative
ring (it will be `H^*(S¹ × S⁵ × Y; ℤ)`) and `φ` any additive map to `ℤ` (it will
be evaluation against the fundamental class; only additivity is used).  Keeping
the seam this abstract is what lets it be checked before either neighbour is
green.
-/

namespace GroupApproximation
namespace STW59

open AlgTop
open AlgTop.MappingTorusParity

/-- **The closing contradiction of Lemma 2.**

If the top Chern number of `W` pairs to an *odd* integer while `W` and `V` satisfy
the hypotheses of Lemma 3, the situation is impossible.  In the application `W` is
the mapping-torus bundle `W_g` built from a hypothetical isomorphism of the
complements, and the odd integer is the count of zeros of the section (2.10),
which is `1`. -/
theorem false_of_parity_of_odd_pairing {S : Type*} [CommRing S]
    (htf : ∀ m : ℕ, m ≠ 0 → ∀ x y : S, (m : S) * x = (m : S) * y → x = y)
    (φ : S →+ ℤ) (W V : TotalChern S) (r : ℕ)
    {ι : Type*} (s : Finset ι) (h : ι → S) (d : ι → ℕ)
    (hVdef : V = ∏ a ∈ s, (TotalChern.line (h a)) ^ (d a))
    (hr : (∑ a ∈ s, d a) < r)
    (hsq : ∀ i j : ℕ, 0 < i → 0 < j →
      (W / V).chernClass i * (W / V).powerSum j = 0)
    (hlow : ∀ q : ℕ, 0 < q → q < 3 → (W / V).powerSum q = 0)
    (hint : ∀ n : ℕ, ∃ w : S,
      (W / V).powerSum (n + 3) = (((n + 3) * ((n + 2) * (n + 1)) : ℕ) : S) * w)
    (hodd : Odd (φ (W.chernClass r))) : False := by
  have heven :=
    even_chernClass_top_pairing_of_sumLine htf φ W V r s h d hVdef hr hsq hlow hint
  rw [Int.even_iff] at heven
  rw [Int.odd_iff] at hodd
  omega

/-- **The contradiction in the manuscript's form.**  The section (2.10) has a
single transverse zero, so its signed count is `±1`; Lemma 3 says the same integer
is even. -/
theorem false_of_parity_of_pairing_eq_one {S : Type*} [CommRing S]
    (htf : ∀ m : ℕ, m ≠ 0 → ∀ x y : S, (m : S) * x = (m : S) * y → x = y)
    (φ : S →+ ℤ) (W V : TotalChern S) (r : ℕ)
    {ι : Type*} (s : Finset ι) (h : ι → S) (d : ι → ℕ)
    (hVdef : V = ∏ a ∈ s, (TotalChern.line (h a)) ^ (d a))
    (hr : (∑ a ∈ s, d a) < r)
    (hsq : ∀ i j : ℕ, 0 < i → 0 < j →
      (W / V).chernClass i * (W / V).powerSum j = 0)
    (hlow : ∀ q : ℕ, 0 < q → q < 3 → (W / V).powerSum q = 0)
    (hint : ∀ n : ℕ, ∃ w : S,
      (W / V).powerSum (n + 3) = (((n + 3) * ((n + 2) * (n + 1)) : ℕ) : S) * w)
    (hone : φ (W.chernClass r) = 1 ∨ φ (W.chernClass r) = -1) : False := by
  have heven :=
    even_chernClass_top_pairing_of_sumLine htf φ W V r s h d hVdef hr hsq hlow hint
  rw [Int.even_iff] at heven
  rcases hone with h1 | h1 <;> rw [h1] at heven <;> omega

end STW59
end GroupApproximation
