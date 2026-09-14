---
rg: 2
id: cantor-crossed-product-idempotent-pairs-are-stable
kind: claim
title: In LC(X,F) ⋊ Z for a minimal Cantor system, aR + eR = R with e idempotent implies a + ec is a unit for some c; regular elements are unit-regular
distinct_from:
  minimal-cantor-crossed-products-stabilize-laurent-pairs: that completes pairs whose second entry is a Laurent polynomial in u, by residues; this completes pairs whose second entry is an idempotent, by internal cancellation.
  minimal-cantor-crossed-product-has-stable-rank-at-most-two: that asks for completion of every unimodular row; this handles idempotent second entries and unit-regularity, and shows stable rank one follows from the exchange property.
artifacts:
  - research/artifacts/sk-algebraic-putnam-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed).** Let `(X,T)` be a minimal homeomorphism of the Cantor set, `F` a field, `R = LC(X,F) ⋊_T Z`.
1. **Idempotent pairs.** If `a ∈ R`, `e = e² ∈ R` and `aR + eR = R`, then `a + ec ∈ R^×` for some `c ∈ R`.
2. **Unit-regularity.** Every von Neumann regular element `a = axa` of `R` is unit-regular: `a = ava` with `v ∈ R^×`.
3. **Conditional stable rank one.** If `R` is an exchange ring, then `sr(R) = 1`. This is Camillo–Yu, Comm. Algebra 22 (1994) 4737–4749, as quoted in arXiv:1402.4706: "in an exchange ring R, every von Neumann regular element is unit regular if and only if R has stable range one".

**Consequence.** The algebraic analogue of Putnam's theorem ("`R` is an exchange ring of stable rank one") is equivalent to the exchange property of `R` alone.

**Proof outline** (artifact §5).
1. With `ar + es = 1`, `α = (1−e)a` and `π = rα`: `π` is idempotent and `π ~ 1−e`. Internal cancellation gives `z ∈ eR(1−π)` and `z′ ∈ (1−π)Re` with `zz′ = e`, `z′z = 1−π`. Then `g = α + z = a + e(z−a)` is a unit with inverse `r(1−e) + z′e`.
2. With `x = xax`: `ax ~ xa`. Internal cancellation gives `s ∈ (1−xa)R(1−ax)` and `t` with `st = 1−xa`, `ts = 1−ax`. Then `v = x + s` is a unit (inverse `a + t`) with `ava = a` (Ehrlich's argument).

**Review (sk-verify-16, 2026-09-13): PASS.** Re-derived: π = rα idempotent with π ~ 1−e; g = α + z = a + e(z−a) with the two-sided inverse r(1−e) + z′e; Ehrlich unit-regularity with v = x + s and inverse a + t. Item 3 is conditional on the Camillo–Yu import. See `research/artifacts/sk-verify-16-2026-09-13-part4.md` §3.
