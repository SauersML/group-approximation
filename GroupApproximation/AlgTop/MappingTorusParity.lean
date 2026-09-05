import GroupApproximation.AlgTop.MappingTorusParityCore
import GroupApproximation.AlgTop.ChernEvenTopClass
import GroupApproximation.AlgTop.ChernPowerSums

/-!
# Lemma 3 of the STW LIX manuscript: mapping-torus parity

Fix `d_1, …, d_ℓ`, put `Y = ∏_j CP^(d_j)`, `m = ∑_j d_j`, `H = ⨁_j L_j^(⊕ d_j)`,
`M = S^5 × Y`, `V = 1^3 ⊕ H` and `r = m + 3`.  Lemma 3 of
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`
says: for **any** complex rank-`r` bundle `W` over `S^1 × M` whose restriction
to the slice `{1} × M` is `V`,

```text
⟨c_r(W), [S^1 × M]⟩ ∈ 2ℤ.                                        (2.3)
```

This module is the assembly.  The parity computation lives in
`GroupApproximation.AlgTop.MappingTorusParityCore` and needs nothing but
Mathlib; the Chern-theoretic scaffolding -- `TotalChern`, Newton's identity in
the cleared form, the closing Whitney step -- is `found-chern-classes`'s and is
imported, not repeated.  Only the two lines of glue are here.

## What the topology lanes owe

`two_dvd_chernClass_top` takes exactly these and nothing else.  Write
`δ = W / V` for the virtual difference; `c(W) = c(p^*V) c(δ)` is then the group
law of `TotalChern S`, so it costs nothing.

* `htf` -- `H^*(S^1 × S^5 × Y; ℤ)` is torsion free, in the form "multiplication
  by a nonzero natural number is injective" (`found-cpn-cohomology`).  This is
  the manuscript's "the calculation in rational cohomology identifies the
  integral coefficients uniquely", and it is the ONLY use torsion-freeness is
  put to.  No rational cohomology ring has to be built;
* `hV : V.chernClass r = 0`.  The manuscript gets this from `dim Y = 2m < 2r`;
  `TotalChern.chernClass_prod_line_pow_eq_zero_of_lt` gets it with no dimension
  count at all, since `c(V)` is a product of `m < r` line classes
  (`found-chern-classes`);
* `hsq` -- `c_i(δ) p_j(δ) = 0` for `i, j > 0`.  This is `z * z = 0` fed through
  `AlgTop.squareZero_of_dvd_squareZero`; `z = t x` and `t ^ 2 = 0` by degree
  (`found-ktheory-bott`);
* `hlow` -- `p_q(δ) = 0` for `0 < q < 3`.  `δ` has rank zero and, by the split
  restriction sequence and the free-case Künneth,
  `ker(K^0(S^1 × M) → K^0(M)) = K^1(S^1) ⊗ K^1(S^5) ⊗ K^0(Y)`, so
  `ch(δ) = z ⬝ ch(β)` with `z` of degree six (`found-ktheory-bott`);
* `hint` -- `p_(n+3)(δ) = (n+3)(n+2)(n+1) ⬝ w_n` for some integral `w_n`.  Since
  `p_q = q ! ch_q`, this says `n ! ⬝ ch_(n+3)(δ)` is an integral class, which in
  the manuscript is the explicit `n ! ch_(n+3)(δ) = z g^n` with
  `g = ∑_j a_j h_j` (`found-ktheory-bott`).  `powerSum_eq_of_chernChar` in the
  core module derives `hint` from that rational description, for a supplier who
  prefers to state it with `ch`.

`even_chernClass_top_pairing` then pairs with the fundamental class through an
additive `φ : S →+ ℤ` (`found-cpn-cohomology`) and delivers (2.3) verbatim.

## Where the delicate normalisation lives

The manuscript flags that the odd `K`-theory generators of `S^1` and `S^5` are
normalised to have Chern characters exactly `t` and `x` -- coefficient `1`, not
`2`.  That normalisation is entirely inside `hint`: it is what makes
`n ! ch_(n+3)(δ)` equal `z g^n` on the nose rather than twice it.  A supplier
delivering the generator with a spare factor of two would only make the parity
stronger, but `hint` is the one place where the constant has to be declared.
-/

namespace GroupApproximation
namespace AlgTop
namespace MappingTorusParity

/-- **The parity of the virtual correction**, on `TotalChern`.  Every positive
Chern class of `δ` is divisible by two.

This is `two_dvd_of_clearedNewton` with Newton's identity supplied by
`TotalChern.natCast_mul_chernClass_of_squareZero`, which already carries the
square-zero collapse. -/
theorem two_dvd_chernClass_of_squareZero {S : Type*} [CommRing S]
    (htf : ∀ m : ℕ, m ≠ 0 → ∀ x y : S, (m : S) * x = (m : S) * y → x = y)
    (δ : TotalChern S)
    (hsq : ∀ i j : ℕ, 0 < i → 0 < j → δ.chernClass i * δ.powerSum j = 0)
    (hlow : ∀ q : ℕ, 0 < q → q < 3 → δ.powerSum q = 0)
    (hint : ∀ n : ℕ, ∃ w : S,
      δ.powerSum (n + 3) = (((n + 3) * ((n + 2) * (n + 1)) : ℕ) : S) * w) :
    ∀ q : ℕ, 0 < q → (2 : S) ∣ δ.chernClass q :=
  two_dvd_of_clearedNewton (c := δ.chernClass) (p := δ.powerSum) htf
    (fun q _ => TotalChern.natCast_mul_chernClass_of_squareZero δ hsq q) hlow hint

/-- **Lemma 3 (mapping-torus parity), in integral cohomology.**  `c_r(W)` is
divisible by two.

Everything topological is in the hypotheses, itemised in the module docstring.
The closing Whitney step is `TotalChern.two_dvd_chernClass_of_div`; the parity
of the virtual correction is `two_dvd_chernClass_of_squareZero`. -/
theorem two_dvd_chernClass_top {S : Type*} [CommRing S]
    (htf : ∀ m : ℕ, m ≠ 0 → ∀ x y : S, (m : S) * x = (m : S) * y → x = y)
    (W V : TotalChern S) (r : ℕ)
    (hV : V.chernClass r = 0)
    (hsq : ∀ i j : ℕ, 0 < i → 0 < j →
      (W / V).chernClass i * (W / V).powerSum j = 0)
    (hlow : ∀ q : ℕ, 0 < q → q < 3 → (W / V).powerSum q = 0)
    (hint : ∀ n : ℕ, ∃ w : S,
      (W / V).powerSum (n + 3) = (((n + 3) * ((n + 2) * (n + 1)) : ℕ) : S) * w) :
    (2 : S) ∣ W.chernClass r :=
  TotalChern.two_dvd_chernClass_of_div W V r hV
    (two_dvd_chernClass_of_squareZero htf (W / V) hsq hlow hint)

/-- **Lemma 3 as the manuscript states it, (2.3).**  Pairing the top Chern class
of `W` against the fundamental class of `S^1 × M` gives an even integer.

`φ` is the evaluation `H^(2r)(S^1 × M; ℤ) → ℤ`; only its additivity is used. -/
theorem even_chernClass_top_pairing {S : Type*} [CommRing S]
    (htf : ∀ m : ℕ, m ≠ 0 → ∀ x y : S, (m : S) * x = (m : S) * y → x = y)
    (φ : S →+ ℤ) (W V : TotalChern S) (r : ℕ)
    (hV : V.chernClass r = 0)
    (hsq : ∀ i j : ℕ, 0 < i → 0 < j →
      (W / V).chernClass i * (W / V).powerSum j = 0)
    (hlow : ∀ q : ℕ, 0 < q → q < 3 → (W / V).powerSum q = 0)
    (hint : ∀ n : ℕ, ∃ w : S,
      (W / V).powerSum (n + 3) = (((n + 3) * ((n + 2) * (n + 1)) : ℕ) : S) * w) :
    Even (φ (W.chernClass r)) :=
  even_map_of_two_dvd φ (two_dvd_chernClass_top htf W V r hV hsq hlow hint)

/-! ## `hV` discharged for the manuscript's `V` -/

/-- **Lemma 3 with `hV` discharged.**  The manuscript's `V = 1^3 ⊕ H` with
`H = ⨁_j L_j^(⊕ d_j)` has total Chern class `∏_j (line h_j)^(d_j)`: the three
trivial summands are the identity of `TotalChern` and drop out.  So
`c_r(V) = 0` as soon as `r > ∑_j d_j`, which `r = m + 3` certainly is.

The manuscript derives `c_r(V) = 0` from `dim Y = 2m < 2r` instead.  That
dimension count is not needed: the vanishing is a statement about the *rank* of
`V`, and holds over any base whatsoever.  Nobody therefore owes Lemma 3 a
dimension bound. -/
theorem two_dvd_chernClass_top_of_sumLine {S : Type*} [CommRing S]
    (htf : ∀ m : ℕ, m ≠ 0 → ∀ x y : S, (m : S) * x = (m : S) * y → x = y)
    (W V : TotalChern S) (r : ℕ) {ι : Type*} (s : Finset ι) (h : ι → S) (d : ι → ℕ)
    (hVdef : V = ∏ a ∈ s, (TotalChern.line (h a)) ^ (d a))
    (hr : (∑ a ∈ s, d a) < r)
    (hsq : ∀ i j : ℕ, 0 < i → 0 < j →
      (W / V).chernClass i * (W / V).powerSum j = 0)
    (hlow : ∀ q : ℕ, 0 < q → q < 3 → (W / V).powerSum q = 0)
    (hint : ∀ n : ℕ, ∃ w : S,
      (W / V).powerSum (n + 3) = (((n + 3) * ((n + 2) * (n + 1)) : ℕ) : S) * w) :
    (2 : S) ∣ W.chernClass r := by
  refine two_dvd_chernClass_top htf W V r ?_ hsq hlow hint
  rw [hVdef]
  exact TotalChern.chernClass_prod_line_pow_eq_zero_of_lt s h d hr

/-- **(2.3) with `hV` discharged.**  `even_chernClass_top_pairing` for the
manuscript's `V`, so that the caller supplies only the `K`-theoretic data. -/
theorem even_chernClass_top_pairing_of_sumLine {S : Type*} [CommRing S]
    (htf : ∀ m : ℕ, m ≠ 0 → ∀ x y : S, (m : S) * x = (m : S) * y → x = y)
    (φ : S →+ ℤ) (W V : TotalChern S) (r : ℕ)
    {ι : Type*} (s : Finset ι) (h : ι → S) (d : ι → ℕ)
    (hVdef : V = ∏ a ∈ s, (TotalChern.line (h a)) ^ (d a))
    (hr : (∑ a ∈ s, d a) < r)
    (hsq : ∀ i j : ℕ, 0 < i → 0 < j →
      (W / V).chernClass i * (W / V).powerSum j = 0)
    (hlow : ∀ q : ℕ, 0 < q → q < 3 → (W / V).powerSum q = 0)
    (hint : ∀ n : ℕ, ∃ w : S,
      (W / V).powerSum (n + 3) = (((n + 3) * ((n + 2) * (n + 1)) : ℕ) : S) * w) :
    Even (φ (W.chernClass r)) :=
  even_map_of_two_dvd φ
    (two_dvd_chernClass_top_of_sumLine htf W V r s h d hVdef hr hsq hlow hint)

end MappingTorusParity
end AlgTop
end GroupApproximation
