---
rg: 2
id: strict-comparison-unit-divisibility-equivalences
kind: claim
title: Under strict comparison, tracial divisibility of the unit, Rordam-Winter divisibility of [1] and unital Z_{n,n+1} maps are equivalent
distinct_from:
  stw99-problem-lxv-jiang-su-embeddings: that asks which unital algebras contain Z itself; this proves, under strict comparison, that divisibility of the unit is equivalent to unital maps from every prime dimension drop algebra, with no coherence into Z.
  stw99-problem-xxvii-comparison-vs-divisibility: that asks whether strict comparison gives almost divisibility of every Cuntz class; this proves equivalences between forms of divisibility of the single class [1] under strict comparison and does not produce any of them.
  bauer-tracially-divisible-unit-gives-bounded-rank-density: that turns a divided unit into rank density on Bauer simplices; this relates the ways a unit can divide, on any trace simplex.
artifacts:
  - research/artifacts/ex-toms-winter-unit-divisibility-equivalences-2026-09-12.md
---

Let `A` be a unital, simple, separable, exact, non-elementary C*-algebra with
`T(A) ≠ ∅` and strict comparison of positive elements. These are equivalent:
1. for every `N` and `ε > 0` there is a c.p.c. order zero map `φ: M_N → A` with
   `τ(φ(1)) > 1 − ε` for all traces (the unit is tracially `N`-divisible);
2. item 1 holds for arbitrarily large `N`;
3. for every `n` there is `x ∈ W(A)` with `n x ≤ [1_A] ≤ (n+1) x`, the divisibility
   property of Rørdam–Winter's Proposition 5.1(i) and Question 5.3;
4. item 3 holds for arbitrarily large `n`;
5. for every `n ≥ 2` there is a unital `*`-homomorphism `Z_{n,n+1} → A`;
6. item 5 holds for arbitrarily large `n`.

**Proof idea.**
- **2 ⇒ 3.** Pick `r/L` strictly between `1/(n+1)` and `1/n`. The element
  `φ(e_11 + ··· + e_rr)` has rank at most `r/L` and trace close to `r/L`, and strict
  comparison turns these bounds into `W(A)` inequalities.
- **4 ⇒ 3.** From level `L` take `z = m x` with `m ∈ [(L+1)/(n+1), L/n]`.
- **3 ⇒ 5.**
  - Level `3n+1` gives `z = 3y` with `n z ≤ [1]` and rank uniformly above `1/(n+1)`.
  - Rørdam's lemma cuts out `n` orthogonal equivalent copies. Rank bookkeeping and
    strict comparison give condition (ii) of Rørdam–Winter's Proposition 5.1.
  - Its implications (ii) ⇒ (iv) need no stable rank one ("The hypothesis of stable
    rank one is only needed for the implication (i) ⇒ (ii)", read verbatim on MSI).
- **6 ⇒ 1.** An explicit order zero `M_N → Z_{n,n+1}` of fibrewise trace at least
  `1 − N/n` (Lemma 3.2 of
  `research/artifacts/ex-toms-winter-bauer-divisible-unit-part2-2026-09-12.md`).

Full proof: Proposition 1 of the artifact. No novelty asserted.

**Consequence.** With `toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`: on
Bauer simplices with tlfnd, Toms–Winter for `A` is equivalent to strict comparison
forcing `n x ≤ [1] ≤ (n+1) x` for every `n`. That is part (1) of STW XXVII at the
single element `1`.
