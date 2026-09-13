# Under strict comparison, tracial divisibility of the unit is Rørdam–Winter divisibility of [1] (2026-09-12)

Lane `ex-toms-winter`. Companion to `research/artifacts/ex-toms-winter-bauer-divisible-unit-2026-09-12.md`
(Definition 1.1, Theorem 1, Theorem 2) and its part 2 (Lemma 3.2).

**Outcome.** Proposition 1 identifies four forms of "the unit divides" under strict comparison.
- On Bauer simplices with tlfnd, Toms–Winter for `A` is therefore equivalent to Rørdam–Winter's
  divisibility property of `[1_A]`: for every `n` some `x ∈ W(A)` has `n x ≤ [1] ≤ (n+1) x`.
- That is part (1) of STW XXVII (strict comparison forces almost divisibility), asked only at
  the unit.
- Nothing is proved about whether strict comparison gives it. Not reviewed.

## Source read

M. Rørdam, W. Winter, *The Jiang–Su algebra revisited*, arXiv:0801.2259, MSI copy
`/projects/standard/hsiehph/sauer354/lit/ex-toms-winter/0801.2259.txt`, lines 455–545 and 800–860.
- **Proposition 5.1**, verbatim: "Let A be a unital C∗-algebra of stable rank one, and let n be a
  natural number. The following four conditions are equivalent:
  - (i) There exists x ∈ W(A) such that nx ≤ ⟨1_A⟩ ≤ (n+1)x.
  - (ii) There exist ε > 0 and mutually equivalent and orthogonal positive elements b1, b2, …, bn
    in A such that 1_A − (b1 + b2 + ··· + bn) ≾ (b1 − ε)_+.
  - (iii) [relations (5.1)]
  - (iv) There is a unital ∗-homomorphism from the C∗-algebra Z_{n,n+1} into A.
  - The hypothesis of stable rank one is only needed for the implication (i) ⇒ (ii)."
- Here `a ∼ b` means `a = x*x` and `b = xx*` for some `x`.
- The proof of (i) ⇒ (ii) uses stable rank one through a cancellation lemma (their Lemma 4.5).
- **Question 5.3** asks whether `Z` embeds unitally when (i) holds for every `n`.
- The text after Remark 5.2 says simple infinite-dimensional algebras can fail (i), citing DHTW.

## Proposition 1

**Proposition 1.** Let `A` be unital, simple, separable, exact and non-elementary, with
`T(A) ≠ ∅` and strict comparison. These are equivalent:
1. for every `N`, the unit is tracially `N`-divisible (Definition 1.1 of the first artifact);
2. the unit is tracially `N`-divisible for arbitrarily large `N`;
3. for every `n ≥ 1` there is `x ∈ W(A)` with `n x ≤ [1] ≤ (n+1) x`;
4. the condition of item 3 holds for arbitrarily large `n`;
5. for every `n ≥ 2` there is a unital `*`-homomorphism `Z_{n,n+1} → A`;
6. the condition of item 5 holds for arbitrarily large `n`.

*Proof.* The implications 1 ⇒ 2, 3 ⇒ 4 and 5 ⇒ 6 are trivial.

**2 ⇒ 3.** Fix `n`.
- Choose `L` with tracial `L`-divisibility and an integer `r` with
  `1/(n+1) < r/L < 1/n`, with room for `ε` below. Take order zero `φ: M_L → A` with
  `τ(φ(1)) > 1 − ε` and put `x_0 = φ(e_11 + ··· + e_rr)`.
- The `L` elements `φ(e_jj)` are orthogonal and mutually equivalent, and they sum to `φ(1)`. So
  `L d_τ(φ(e_11)) ≤ 1` and `d_τ(x_0) ≤ r/L < 1/n`.
- Also `d_τ(x_0) ≥ τ(x_0) = r τ(φ(1))/L > r(1 − ε)/L > 1/(n+1)` for `ε` small.
- Strict comparison gives `n [x_0] ≤ [1]` and `[1] ≤ (n+1)[x_0]`.

**4 ⇒ 3.** Level reduction.
- Suppose `L x ≤ [1] ≤ (L+1) x` and `L ≥ n(n+1) + n`. The interval `[(L+1)/(n+1), L/n]` has
  length `(L − n)/(n(n+1)) ≥ 1`, so it contains an integer `m`.
- Then `z = m x` has `n z ≤ L x ≤ [1]` and `[1] ≤ (L+1) x ≤ (n+1) z`.

**3 ⇒ 5.** Fix `n ≥ 2`.
- **A margin.** Item 3 at level `3n+1` gives `y` with `(3n+1) y ≤ [1] ≤ (3n+2) y`. Put `z = 3y`.
  Then `n z ≤ [1]` in `W(A)`, and `d_τ(z) ≥ 3/(3n+2) = 1/(n+1) + c` with `c > 0`.
- **A cut-down.** Represent `z` by a contraction `d ∈ M_k(A)_+`. Every `d_τ((d − δ)_+)` is lower
  semicontinuous in `τ` and increases to `d_τ(d)`, and `T(A)` is compact. So some `δ > 0` has
  `d_τ((d − δ)_+) > 1/(n+1)` for every `τ`.
- **Orthogonal copies.** Since `⊕^n d ≾ 1_A`, Rørdam's lemma gives a row `t = (t_1, …, t_n)` with
  `t*t = ⊕^n (d − δ/2)_+`. Put `g = (d − δ/2)_+` and `e_j = t_j t_j*`.
  - The `e_j` are pairwise orthogonal, because `t_i*t_j = 0` for `i ≠ j`, and `t_j*t_j = g`.
- **The elements `b_j`.** Let `η = δ/2`. Let `f` vanish on `[0, η/2]`, rise linearly to `1` at `η`,
  and equal `1` beyond, and put `b_j = f(e_j)`.
  - With polar decompositions `t_j = v_j g^{1/2}`, `x_j = t_j m(g) t_1*` with
    `m(t) = f(t)^{1/2}/t` lies in `A`, since `m` is continuous and vanishes near `0`.
  - It satisfies `x_j*x_j = f(e_1) = b_1` and `x_jx_j* = f(e_j) = b_j`. So the `b_j` are mutually
    equivalent and orthogonal, and `Σ_j b_j = f(e)` with `e = Σ_j e_j`.
- **Ranks.** `1 − f(e)` is supported where the spectrum of `e` is below `η`. So
  `d_τ(1 − f(e)) ≤ 1 − d_τ((e − η)_+) = 1 − n D(τ)`, where
  `D(τ) = d_τ((e_1 − η)_+) = d_τ((d − δ)_+) > 1/(n+1)`.
  - For `0 < ε' < 1`, `(b_1 − ε')_+` is supported where the spectrum of `e_1` is above `η/2`, so
    its rank is at least `D(τ)`.
  - Hence `d_τ(1 − Σ_j b_j) ≤ 1 − nD(τ) < D(τ) ≤ d_τ((b_1 − ε')_+)` for every `τ`.
- **Conclusion.** Strict comparison gives condition (ii) of Rørdam–Winter's Proposition 5.1. Its
  implications (ii) ⇒ (iii) ⇒ (iv) need no stable rank one, and give a unital `Z_{n,n+1} → A`.

**6 ⇒ 1.** Lemma 3.2 of part 2: a unital `Z_{n,n+1} ⊂ A` gives order zero `M_N → A` with trace at
least `1 − N/n` at every trace. Let `n → ∞` along the given sequence. ∎

## Consequences

- **Theorem 2 of the first artifact, extended.** Let `A` be unital, simple, separable, nuclear
  and non-elementary, with Bauer `T(A)`, tlfnd and strict comparison. Then `A ≅ A ⊗ Z` iff for
  every `n` some `x ∈ W(A)` has `n x ≤ [1] ≤ (n+1) x`, iff unital `Z_{n,n+1} → A` exist for
  arbitrarily large `n`.
- **Purity on Bauer simplices, no nuclearity.** Let `A` be exact with Bauer `T(A)` and
  strict comparison. Theorem 1 of the first artifact turns (1) into RD_b, and the spectral
  estimates turn RD_b into rank density. Then `rank-density-and-strict-comparison-give-purity`
  gives purity. Conversely purity gives (3) at the compact class `[1]`. So `A` is pure iff
  `[1_A]` is almost divisible (`bauer-strict-comparison-pure-iff-divisible-unit`).
- **The crux as part (1) of STW XXVII at one element.** Purity asks almost divisibility of every
  Cuntz class. On this locus, strict comparison plus almost divisibility of `[1]` alone gives
  RD_b (Theorem 1), then purity (`rank-density-and-strict-comparison-give-purity`), then
  `Z`-stability. So `strict-comparison-forces-tracially-divisible-unit` is exactly: strict
  comparison forces Rørdam–Winter divisibility of the unit.
- **What fails in DHTW's algebra.** It is simple and nuclear with no unital `Z_{3,4}`, so it fails
  (3) at level `3`. Item 5 at level `3` is (3) at level `3` for any unital algebra, by
  Rørdam–Winter (iv) ⇒ (i), which is their reference [15, Lemma 4.2]. Without strict comparison,
  Proposition 1 was not examined.
- **Rørdam–Winter Question 5.3.** Under strict comparison, the hypothesis of that question already
  gives unital maps from every `Z_{n,n+1}`, and so tracially large order zero maps from every
  `M_N`. Coherence, getting `Z` itself, was not examined.

## Trust surfaces

- Rørdam's lemma (Cuntz subequivalence gives `x` with `x*x = (a − ε)_+` and `xx*` in the
  hereditary subalgebra of `b`) and functional calculus on `x*x` versus `xx*` are standard and were
  not re-read.
- Rørdam–Winter Proposition 5.1 and the stable-rank-one remark were read verbatim.
- Not reviewed. No novelty asserted: this is Rørdam–Winter's Proposition 5.1, with strict
  comparison replacing stable rank one in (i) ⇒ (ii), plus elementary rank bookkeeping.
