---
rg: 2
id: bernoulli-product-traces-have-finite-cylinder-form
kind: claim
title: "Independent product traces on torsion-free full shifts are finite cylinder formulas"
distinct_from:
  bernoulli-algebraic-idempotent-traces-reduce-to-the-host: "That treats algebraic idempotents; this covers every reduced-C*-algebra K-class through relative spectral traces."
  bernoulli-product-traces-kill-rank-invisible-k0: "That annihilates only the rank-invisible subgroup for arbitrary hosts; this uses torsion-free locality to compute every product trace."
artifacts:
  - research/artifacts/bc-bernoulli-product-traces-2026-09-20.md
---


For countable torsion-free G, finite Λ with 0, and
A=C_0(Λ^G\{0})⋊_rG, let `N(y)=(n_[s](y))` be the finite Möbius pattern
expansion. For any probability ν on Λ and any y∈K_0(A),

```text
τ_(ν^G)(y)=Σ_[s] n_[s](y) ∏_(v∈F_s) ν(s(v)).
```

Only finitely many terms occur. For uniform measure on p symbols,
the ideal trace range is contained in ℤ[1/p], and equals it if G is
infinite. This is a statement about all analytic K-classes, extending
the existing algebraic-idempotent trace computation.
