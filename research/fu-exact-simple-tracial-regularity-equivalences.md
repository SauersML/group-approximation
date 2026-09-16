---
rg: 2
id: fu-exact-simple-tracial-regularity-equivalences
kind: claim
title: For exact algebraically simple algebras, tracial m-almost divisibility, property (TM) and real rank zero of the tracial sequence algebra coincide (Fu)
distinct_from:
  fu-locally-finite-nucdim-completions-have-only-uniform-traces: that is a different Fu theorem, on uniform tracial completions of stable-rank-one algebras with locally finite nuclear dimension; this is Fu's 2026 equivalence of tracial divisibility properties for exact simple algebras, with no stable rank or dimension hypothesis.
  stw27-real-rank-zero-almost-divisibility: that derives almost divisibility of Cu(A) from real rank zero of A itself; this concerns real rank zero of the tracial sequence algebra and order zero tracial divisibility, and the implication from Cu-divisibility goes the other way.
  strict-comparison-rank-surjectivity-forces-sr1: that is Lin's theorem and needs strict comparison; this has no comparison hypothesis and does not mention stable rank.
artifacts:
  - research/artifacts/stw18-k1-witness-tracial-divisibility-2026-09-16.md
---

Let `A` be an algebraically simple, separable, non-elementary, exact
C*-algebra with `QT~(A) ≠ {0}`. The following are equivalent:

1. `Γ: Cu(A) → LAff_+(QT~(A))` is hereditary dense;
2. `A` has tracial approximate oscillation zero;
3. `l^∞(A)/J_A` has real rank zero, where `J_A` is the trace kernel ideal;
4. `A` is tracially diagonally divisible;
5. `A` has Property (TM);
6. `A` is tracially almost divisible;
7. `A` is tracially `m`-almost divisible for some `m ≥ 0`;
8. `A` is weakly tracially diagonally divisible.

Without exactness the chain (1)⇒(2)⇔(3)⇒(4)⇒(5)⇒(6)⇒(7) still holds.

Also, if `A` is algebraically simple, separable and exact with `QT(A) ≠ ∅`, and
`Cu(A)` is `m`-almost divisible for some `m`, then (3) holds.

**The definitions used downstream.** `QT(A)` is the set of `τ ∈ QT~(A)` with
`‖τ|_A‖ = 1`. On `Ped(A⊗K)`, `‖x‖_2` is `sup τ(x*x)^{1/2}` over the weak* closure
of `QT(A)`.

- **(5) Property (TM).** For all `a ∈ Ped(A⊗K)^1_+`, `n` and `ε > 0` there is a
  c.p.c. order zero `φ: M_n → Her(a)` with `‖φ(1_n)a − a‖_2 < ε`.
- **(7) Tracially `m`-almost divisible.** For all `k`, positive contractions
  `a ∈ M_k(A)`, `n` and `ε > 0` there is a c.p.c. order zero `φ: M_n → Her(a)`
  with `τ(φ(1_n)) ≥ τ(a)/(m+1) − ε` for all `τ ∈ QT(A)`.
- **(6)** is (7) with `m = 0`.
- **`m`-almost divisible `Cu(A)`.** For all `a ∈ M_∞(A)_+` and `k` there is
  `x ∈ Cu(A)` with `kx ≤ [a] ≤ (k+1)(m+1)x`.
