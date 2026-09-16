---
rg: 2
id: stw18-k1-witness-not-tracially-almost-divisible-proof
kind: route
title: Any divisibility would give stable rank one, which a K1-witness lacks
target: stw18-k1-witness-not-tracially-almost-divisible
requires: [stw18-k1-witness-constraints, strict-comparison-tracial-divisibility-forces-sr1]
artifacts:
  - research/artifacts/stw18-k1-witness-tracial-divisibility-2026-09-16.md
---

Let `A` be as in the target.

**The hypotheses of `strict-comparison-tracial-divisibility-forces-sr1`.**

- **Exact.** `A` is nuclear, hence exact.
- **`T(A) ≠ ∅`.** The trace simplex is nonempty.
- **Strict comparison.** The target's strict comparison of positive elements
  against the trace simplex is the hypothesis stated there: for
  `a, b ∈ M_∞(A)_+`, `d_τ(a) < d_τ(b)` for all `τ ∈ T(A)` implies `a ≲ b`. The
  stronger form for `A⊗K` against all quasitraces implies it.
- **The rest.** Unital, simple, separable and non-elementary are assumed.

**The failures.** Items 1–4 of the target are cases (a), (b), (c) and (d) of
`strict-comparison-tracial-divisibility-forces-sr1`. If any held, that claim
would give `sr(A) = 1`. Item 2 of `stw18-k1-witness-constraints` says
`sr(A) ≥ 2`. So all four fail.

**The concrete form.** This is the negation of item 2 at each fixed `m`:

- by Step 0 of `strict-comparison-tracial-divisibility-sr1-proof`, the
  quasitraces in Winter's definition are the traces;
- in Winter's definition the order zero map may depend on `(a, n, ε)`, and it
  must satisfy the inequality for all `τ` at once. So its negation at fixed `m`
  gives `(a, n, ε)` such that no c.p.c. order zero `φ: M_n → her(a)` satisfies
  it for all `τ`. That is, every such `φ` has
  `τ(φ(1_n)) < τ(a)/(m+1) − ε` for some `τ ∈ T(A)`.

**The firewall.** STW Problem XXVIII only makes sense for positive
contractions. Read literally, for `a = 2·1_A` and `ε < 1` it holds for no unital
`A` with traces, because a c.p.c. `φ` has `τ(φ(1_n)) ≤ 1 < 2 − ε`. On
contractions, the XXVIII hypothesis is item 3, which fails. So no witness
satisfies the XXVIII hypothesis. A witness is therefore never a counterexample
to XXVIII, and a positive answer to XXVIII says nothing about a witness.
