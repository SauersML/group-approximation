---
rg: 2
id: bounded-removal-finite-quotient-caps-cocycle-cheeger
kind: claim
title: A finite quotient detecting one of t removed triangles caps the permutation cocycle Cheeger constant at t over the triangle count
distinct_from:
  finite-quotient-caps-cocycle-cheeger-constant: that is the case of one removed triangle, with the detecting quotient taken for the complex minus that triangle; this removes a set of t triangles chosen freely, and the cap grows only linearly in t
  random-complex-cocycle-cheeger-beats-triangle-count: that is the open Chapman--Peled lower bound for random complexes; this is an unconditional deterministic upper bound, which that lower bound must survive for every bounded removal
artifacts:
  - research/artifacts/chapman-peled-2509-21566-verified-2026-09-11.md
---

**ESTABLISHED.** Let `Y' ⊂ Z` be pure connected 2-dimensional simplicial
complexes with the same 1-skeleton and `Z(2) = Y'(2) ⊔ T`, `|T| = t >= 1`. Give
each complex the uniform measure on its triangles and the descending edge and
vertex measures. Suppose

* `Y'` is a λ-local spectral expander for some `λ < 1/2`, and
* for some `Δ in T`, the perimeter of `Δ` survives in some finite quotient of
  `π_1(Y')`.

Then

```text
h_1(Z, Sym) <= (2 - 2λ) t / ((1 - 2λ) |Y'(2)|).                  (FQC_t)
```

For `t = 1` this is `finite-quotient-caps-cocycle-cheeger-constant`.

## Why it matters

`T` may be chosen after seeing `Z`. So refuting the Chapman--Peled hypothesis
at a complex `Z` needs only *some* bounded set of its triangles whose removal
leaves an expander in which one removed perimeter is detected by a finite
quotient. A random missing triangle is not required.

The quotients involved are quotients of `π_1(Z \ T)`, which surjects onto
`π_1(Z)`. A detecting quotient does not factor through `π_1(Z)`, since it sends a
relator of `π_1(Z)` to a nontrivial element. So the polynomial-quotient
exclusion for `π_1(Z)` in `meshulam-random-complex-no-polynomial-quotients` does not
apply to it as stated.

No novelty is claimed. The proof is the one-triangle argument run with `t`
violated triangles.

DERIVATION
bounded-removal-finite-quotient-cheeger-cap-proof
