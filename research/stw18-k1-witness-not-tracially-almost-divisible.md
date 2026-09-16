---
rg: 2
id: stw18-k1-witness-not-tracially-almost-divisible
kind: claim
title: A strict-comparison K1-witness has no tracial or Cuntz-semigroup divisibility of any order and is no test object for STW Problem XXVIII
distinct_from:
  stw18-k1-witness-constraints: that records stable rank at least two, a rank gap, non-purity and the trace-simplex restrictions; this adds the order zero tracial failures, uniform in the loss constant m, the failure of real rank zero for the tracial sequence algebra, and the firewall with Problem XXVIII.
  stw18-k1-witness-strict-comparison-not-k1-injective: that asks for a witness; this proves what any witness must lack.
  stw99-problem-xxviii-tracial-divisibility-gamma: that asks whether Winter's tracial divisibility gives uniform property Gamma; this shows a K1-witness never has that divisibility, so neither problem constrains the other through such an algebra.
  strict-comparison-forces-tracially-divisible-unit: that concerns dividing the single element 1_A; this concerns dividing all positive contractions of all matrix algebras, and says nothing about the unit.
artifacts:
  - research/artifacts/stw18-k1-witness-tracial-divisibility-2026-09-16.md
---

Let `A` be simple, separable, unital, nuclear and non-elementary, with strict
comparison of positive elements against a nonempty trace simplex. Suppose `A`
is not K1-injective. Then all of the following fail:

1. `W(A)` is `m`-almost divisible, for any `m ≥ 0`;
2. `A` is tracially `m`-almost divisible in Winter's sense, for any `m ≥ 0`;
3. `A` has Winter's tracial divisibility property as stated in STW Problem
   XXVIII, for positive contractions;
4. any of Fu's eight properties
   (`fu-exact-simple-tracial-regularity-equivalences`):
   - real rank zero of `l^∞(A)/J_A`;
   - Property (TM);
   - hereditary density of `Γ`;
   - tracial approximate oscillation zero;
   - tracial diagonal divisibility.

Concretely, for every `m ≥ 0` there are a positive contraction `a ∈ M_k(A)`,
`n` and `ε > 0` such that every c.p.c. order zero `φ: M_n → her(a)` has
`τ(φ(1_n)) < τ(a)/(m+1) − ε` for some `τ ∈ T(A)`.

In particular no such `A` satisfies the hypothesis of STW Problem XXVIII,
read for positive contractions. So a witness is never a counterexample to
XXVIII, and a positive answer to XXVIII says nothing about a witness.
