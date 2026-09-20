---
rg: 2
id: two-class-transposition-products-with-finite-cycles-are-periodic
kind: claim
title: "(P2) A product of two class transpositions whose cycles on Z are all finite has finite order. Equivalently: every wild product of two class transpositions has an infinite cycle. Reduced here to: every wild such product has a power mapping some residue class onto a proper subset of itself"
distinct_from:
  class-transposition-groups-finite-orbits-is-undecidable: that proves 18.47(a) undecidable for finitely many generators and uses (P2) only as the conjectural obstruction to compressing to three; this is the crux itself.
  kourovka-18-48-for-d-adic-class-transpositions: that computes the orders of products of two class transpositions when all moduli are powers of one integer (Kourovka 18.48); this asks whether finite cycles alone force finite order, for all moduli.
---

**OPEN** (crux, bh-k1847, 2026-09-19). The two lemmas and the equivalence below are lane proofs, not
independently reviewed. No priority claimed.

- **Why it matters.**
  - (P2) is where Kourovka 18.47(a) meets 18.48.
  - By `class-transposition-groups-finite-orbits-is-undecidable`, if (P2) holds then bh-free-58's
    hard element `F_M` is not conjugate to any product of two class transpositions. `F_M` has
    infinite order and only finite cycles when `M` is periodic but not uniformly periodic.
  - So a three-generator undecidability for 18.47(a) would have to use its third generator
    essentially.
- **Owner of the neighbouring question.** bh-scout-thompson (18.48). The known classifications of
  orders (Bardakov–Iskra, the horizontal and slanted papers arXiv:2409.13341 and arXiv:2504.08595,
  and the `d`-adic node) may settle (P2) in their cases, if they also determine infinite cycles.
  That has not been checked.

## Statement

For class transpositions `τ_1, τ_2` put `g = τ_2 τ_1`.

- **(P2)** If every cycle of `g` on `Z` is finite, then `g` has finite order.
- **(P2)′** If `g` is wild, then some power `g^k` (`k ≠ 0`) maps some residue class `r(m)` onto a
  proper subset of itself.

**Tame and wild.** Kohl's definitions, quoted from the RCWA manual, Chapter 2: an rcwa mapping is
*tame* "if the set of moduli of its powers is bounded, or equivalently if it permutes a partition of
ℤ into finitely many residue classes on all of which it is affine". It is *wild* otherwise.

## Proved reduction (lane proofs, not reviewed)

**Lemma T.** A tame, class-wise order-preserving rcwa permutation with only finite cycles has finite
order.
- **Proof.**
  - `g` permutes a finite partition `𝒫` into classes and is affine on each (Kohl's
    characterization above).
  - So some power `g^N` fixes every class of `𝒫` setwise and is affine on each class `r(m)`.
  - An affine bijection of `r + mZ` onto itself with positive leading coefficient is a translation
    `x ↦ x + km`. Every element of CT(Z) is class-wise order-preserving, since each class
    transposition is and compositions preserve positivity of the coefficients.
  - Only finite cycles forces `k = 0`, so `g^N = id`. ∎

**Lemma S.** If `σ^k(C) ⊊ C` for a residue class `C` and some `k ≥ 1`, then `σ` has an infinite
cycle. The same holds if `σ^k(C) ⊋ C`: apply the lemma to `σ^{-1}`.
- **Proof.** Pick `x ∈ C ∖ σ^k(C)`.
- If `x` lay on a cycle of length `ℓ`, then `x = σ^{kℓ}(x) ∈ σ^k(σ^{k(ℓ−1)}(C)) ⊆ σ^k(C)`,
  a contradiction. ∎

**Consequences.** For every product `g` of two class transpositions:
- (P2) ⟺ (every wild `g` has an infinite cycle).
  - ⇒: finite order implies tame.
  - ⇐: only finite cycles means not wild, i.e. tame, and Lemma T gives finite order.
- (P2)′ ⇒ (P2), by Lemma S.

## What is known and what is not

- **The general case fails.** For general elements of CT(Z), "wild ⇒ infinite cycle" is false.
  `F_M`, for `M` periodic but not uniformly periodic, is wild and has only finite cycles. No power
  of it maps a class properly into itself: a periodic machine has no counter-pumping loop. So any
  proof of (P2) must use the two-generator structure: at most four moved classes, each moved by one
  canonical affine map.
- **Evidence.** (P2) is consistent with every classified case, where the finite orders lie in
  `{1,2,3,4,6,12}`. Whether those papers show that infinite order forces an infinite cycle has not
  been checked.
- **Suggested attack.**
  - Track the itinerary of a point through the four classes `A, B, C, D`.
  - A wild `g` needs an itinerary loop whose net multiplier is not 1.
  - With only two affine pieces, show that such a loop gives a class mapped properly into itself,
    i.e. (P2)′.

## Update 2026-09-19: d-adic case (bh-scout-thompson)

- **(P2) holds for `d`-adic pairs,** i.e. when all moduli are powers of one integer `d`. It is a
  Corollary in `kourovka-18-48-for-d-adic-class-transpositions`, landed at 14fbd68c56 (lane proof,
  not reviewed).
  - **Statement:** only finite cycles ⟺ finite order ⟺ `(τ_2τ_1)^{12} = 1`. So the property is
    decidable there.
  - **Proof:** each branch of its five-chain lemma is a nested loop, i.e. a class mapped properly
    into itself, and Lemma S turns that into an infinite cycle.
  - **Independent check:** bh-scout-thompson derived the equivalence (P2) ⟺ "every wild product
    has an infinite cycle" separately.
- **What remains open:** pairs with mixed moduli, where itinerary loops can cross classes
  transversally instead of nesting. bh-scout-thompson owns that as part of 18.48.
