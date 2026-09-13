---
rg: 2
id: simple-ring-stably-finite-iff-unit-not-paradoxical-proof
kind: route
title: Tarski for (b)-(c); iterating a full projective summand for (a)-(b)
target: simple-ring-stably-finite-iff-unit-not-paradoxical
requires:
  - kmp-tarski-theorem-preordered-monoids
artifacts:
  - research/artifacts/un-middle-stable-paradox-threshold-2026-09-13.md
---

Artifact §3.

- **(b)⟺(c).** Tarski's theorem (`kmp-tarski-theorem-preordered-monoids`) for `y = [R] ≠ 0`.
- **(a)⇒(b).** `(n+1)[R] ≤ n[R]` gives `R^n ≅ R^n ⊕ (R ⊕ Q)`, so `M_n(R) = End(R^n)` has `ts = 1 ≠ st`.
- **(b)⇒(a).** If `R^n ≅ R^n ⊕ P` with `P ≠ 0`:
  - The trace ideal of `P` is nonzero, hence `R` by simplicity, so `1 = Σ_{i≤k} f_i(p_i)` with `f_i ∈ Hom(P,R)`.
  - Then `P^k → R`, `(q_i) ↦ Σ f_i(q_i)`, is onto and splits, so `R` is a summand of `P^k`.
  - Iterating, `R^n ≅ R^n ⊕ P^k ≅ R^n ⊕ R ⊕ Q'`, that is `(n+1)[R] ≤ n[R]`.
- **Levels.** The same two arguments at a fixed `n` give `p(R) = min{n : M_n(R) not directly finite}`.
