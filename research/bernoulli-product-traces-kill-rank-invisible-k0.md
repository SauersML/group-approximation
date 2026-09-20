---
rg: 2
id: bernoulli-product-traces-kill-rank-invisible-k0
kind: claim
title: "Every independent product trace kills rank-invisible degree-zero K-theory of a punctured full shift"
distinct_from:
  bernoulli-pattern-expansions-are-finite: "That controls finite-configuration ranks and their pattern coefficients; this controls independent product traces of the virtual remainder."
artifacts:
  - research/artifacts/bc-bernoulli-product-traces-2026-09-20.md
---


Let G be any countable discrete group, Λ a finite alphabet with 0,
X=Λ^G, A=C_0(X\{0})⋊_rG, and r_x the compact-orbit rank at a
finite-support configuration. For every probability ν on Λ,

```text
τ_(ν^G)(y)=0  whenever y∈⋂_(x of finite support) ker r_x ⊆ K_0(A).
```

All matrix traces are unnormalized. Torsion-freeness is not needed
for this assertion. Full-shift density and independence are essential
to the proof given here; no assertion is made for correlated invariant
measures or arbitrary subshifts. Trace invisibility is not vanishing
of the virtual class. Nothing here decides K_1(A).

The [torus line-bundle example](torus-has-nonzero-k0-class-invisible-to-every-trace.md)
is a concrete nonzero virtual class invisible even to all tracial states.
The [module quotient all-trace theorem](module-quotient-k0-defects-are-trace-invisible.md)
concerns a different quotient setting and does not extend this Bernoulli
product-measure result to arbitrary correlated measures. Neither result
proves that the respective K-theory remainder vanishes.
