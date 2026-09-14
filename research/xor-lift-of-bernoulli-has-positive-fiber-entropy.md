---
rg: 2
id: xor-lift-of-bernoulli-has-positive-fiber-entropy
kind: claim
title: The XOR automaton over the integers lifts uniform Bernoulli with conditional entropy log 2
invalidates: [gottschalk-via-flip-lift-and-zero-fiber-entropy]
distinct_from:
  ca-bernoulli-lifts-have-zero-fiber-entropy: that is the universal zero-entropy statement; this is the counterexample refuting it.
  strict-split-pairs-carry-positive-entropy-flip-lifts: that derives positive fiber entropy from a strict split pair; this exhibits positive fiber entropy over a surjunctive group, where no strict pair exists.
artifacts:
  - research/artifacts/decoder-fiber-flip-lifts-2026-09-12.md
---

Let `G = Z`, `A = Z/2`, `lambda` uniform Bernoulli, and
`sigma(x)(n) = x(n) + x(n+1)`. Then

    sigma_* lambda = lambda,      H_lambda( x(0) | sigma^-1(Borel) ) = log 2.

Onto linear maps on finite windows push uniform to uniform. The global flip
`x -> x + 1` preserves `lambda` and `sigma`, so `x(0)` is a fair bit given
`sigma(x)`.

`Z` is surjunctive. So a positive single-site conditional entropy of an
invariant lift of uniform Bernoulli contradicts nothing, and the flip lift of
`strict-split-pairs-carry-positive-entropy-flip-lifts` does not refute strictness
by itself. What the amenable proof uses is a Følner average. Over `F_2` the
Ornstein–Weiss block map shows that averaging is unavailable. Section 4 of the
artifact has both proofs.
