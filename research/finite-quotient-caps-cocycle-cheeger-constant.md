---
rg: 2
id: finite-quotient-caps-cocycle-cheeger-constant
kind: claim
title: A finite quotient detecting a removed triangle caps the permutation cocycle Cheeger constant
distinct_from:
  random-complex-linear-cocycle-stability: that is the open probabilistic lower bound for random Linial--Meshulam complexes; this is an unconditional deterministic upper bound for one pair of complexes, which any such lower bound must survive
  sofic-stable-implies-residually-finite: that is the soft sofic-plus-stable principle with no expansion input; this is a quantitative cap that uses local spectral expansion and never mentions soficity
artifacts:
  - research/artifacts/chapman-peled-2509-21566-verified-2026-09-11.md
---

**ESTABLISHED.** Let `Y ⊂ Z` be pure connected 2-dimensional simplicial
complexes with the same 1-skeleton and `Z(2) = Y(2) ⊔ {Δ}`. Give each complex
the uniform measure on its triangles and the descending edge and vertex
measures. Suppose

* `Y` is a λ-local spectral expander for some `λ < 1/2`, and
* the perimeter of `Δ` survives in some finite quotient of `π_1(Y)`.

Then

```text
h_1(Z, Sym) <= (2 - 2λ) / ((1 - 2λ) |Y(2)|).          (FQC)
```

Equivalently: if `h_1(Z,Sym) > (2-2λ)/((1-2λ)|Y(2)|)`, the perimeter of every
such `Δ` lies in the finite residual of `π_1(Y)`.

## Why it matters

Chapman--Peled's mid-range hypothesis is `h_1 = ω(n^(-3)p^(-1))`, and
`|Y(2)| ~ p·C(n,3)`. So their hypothesis is precisely the failure of (FQC) at a
random missing triangle. It is therefore at least as strong as a finite-residual
statement about the random hyperbolic group `π_1(Y)`. No argument that leaves
the finite quotients of `π_1(Y)` untouched can prove it. In the other direction,
each finite quotient that detects a random missing triangle refutes it at that
complex.

This is the second use of the same estimate. With the mid-range properties it
reaches `non-residually-finite-hyperbolic-group` directly
(`non-rf-hyperbolic-via-cheeger-threshold`), with no soficity and no
Glebsky--Rivera step.

DERIVATION
finite-quotient-caps-cocycle-cheeger-constant-proof
