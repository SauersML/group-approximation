---
rg: 2
id: injective-limit-trace-flexible-hs-repair-is-strict
kind: claim
title: A flexibly repairable asymptotic representation whose limit trace generates an injective algebra is strictly repairable
distinct_from:
  sl2-half-explicit-strict-flexible-separation: that gives one explicit sequence for PSL_2(Z[1/2]) that same-dimensional repair cannot fix but one added dimension does; this proves that any such sequence, for any finitely generated group, has a limit trace generating a non-injective von Neumann algebra.
  kazhdan-weak-ucp-stability-is-flexible-stability: that upgrades weak ucp-stability to flexible stability for hyperlinear Kazhdan groups; this upgrades flexible repair to same-dimensional repair, under an injectivity hypothesis that fails for the regular trace of every infinite Kazhdan group.
  hyperlinear-flexibly-hs-stable-group-is-residually-finite: that reads residual finiteness off flexible stability of a separating approximation; this compares flexible and strict repair of one fixed approximation.
---

**ESTABLISHED.** Let `Γ` be a finitely generated group with a finite symmetric
generating set `S`, and let `α_n : Γ -> U(d_n)` be an asymptotic homomorphism
in the sense of Dogon arXiv:2211.10492v3 Definition 1.2:
`||α_n(g)α_n(h) - α_n(gh)||_2 -> 0` for all `g,h`, with normalized
Hilbert--Schmidt norm. Fix a nonprincipal ultrafilter `ω` on `N`. Put
`τ(g) = lim_ω tr α_n(g)`, a character of `Γ`, and let
`L_τ(Γ) = π_τ(Γ)''` be the von Neumann algebra of its GNS representation.
Assume:

```text
(F) there are homomorphisms π_n : Γ -> U(D_n), D_n >= d_n, lim_ω D_n/d_n = 1,
    with lim_ω || α_n(g) - P_n π_n(g) P_n ||_(2,d_n) = 0 for every g,
    where P_n is the projection onto the first d_n coordinates;
(I) L_τ(Γ) is injective.
```

Then there are homomorphisms `ρ_n : Γ -> U(d_n)`, of the same dimension, with
`lim_ω ||α_n(g) - ρ_n(g)||_2 = 0` for every `g`.

So a flexible correction along `ω` can be traded for a same-dimensional one
whenever the limit trace is amenable in this sense. Two consequences:

1. **Group level.** For a finitely generated group whose maximal almost
   periodic quotient is amenable, flexible HS-stability equals HS-stability
   (`amenable-flexible-hs-stability-is-strict-hs-stability`).
2. **Where separations live.** If (F) holds along `ω` and same-dimensional
   repair fails along `ω`, then `L_τ(Γ)` is not injective. The sequence of
   `sl2-half-explicit-strict-flexible-separation` satisfies (F) along every
   `ω`: (SFS3) bounds the zero-padding distance, and
   `flexible-hs-metric-controls-words-and-padding` turns that bound into
   `D/d -> 1` and compression closeness. By (SFS2), same-dimensional repair
   fails along every `ω`. So every limit trace of that sequence generates a
   non-injective algebra.

The proof: move the trace from the compressions to the genuine
representations, pad fixed finite-dimensional representations with trivial
summands to reach exactly `d_n`, and conjugate the two resulting matrix
microstates onto each other with Jung's tubularity theorem for injective
algebras (arXiv:math/0506108).

DERIVATION
injective-limit-trace-flexible-hs-repair-is-strict-proof
