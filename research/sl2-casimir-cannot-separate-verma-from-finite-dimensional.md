---
rg: 2
id: sl2-casimir-cannot-separate-verma-from-finite-dimensional
kind: claim
title: The Casimir element and its resolvents act by equal scalars on L(k) and on the Verma submodule of M(k), so no central relation kills Verma-type modules
distinct_from:
  sl2-vacuum-hosts-admit-verma-type-modules: that is the ring-level obstruction, that a finitely presented sl_2 vacuum ring admits Verma-type modules; this is the representation-theoretic fact that the Casimir cannot separate them, which that obstruction uses.
  capacity-chain-presentation-is-not-simple: that refutes the two-register capacity presentation through a bi-infinite capacity chain; this refutes the specific Casimir fix for the sl_2 design.
artifacts:
  - research/artifacts/gq-gq-k2-q-sl2-verma.md
---

**ESTABLISHED (2026-09-18, lane gq-k2-q).** Standard `sl_2` representation theory
(Bernstein–Gelfand–Gelfand; Humphreys, *Representations of Semisimple Lie Algebras in the BGG Category O*, §1). No
novelty. Recorded because it decides Attempt 4 of `fp-simple-resolvent-ring-with-divisible-unit-class`.

## Setting

`sl_2` over `Q`: generators `e, f, h`, relations `[h,e] = 2e`, `[h,f] = -2f`, `[e,f] = h`. The Casimir element is
`Ω = ef + fe + ½ h² = 2 fe + h + ½ h²`, which is central in the enveloping algebra `U`.

For `λ ∈ Q`, `M(λ)` is the Verma module (highest weight `λ`, basis `f^i v_λ`, `i >= 0`, infinite dimensional).
For `k ∈ {0,1,2,...}`, `L(k) = M(k)/M(-k-2)` is the irreducible of dimension `k+1`.

## Statement

1. **Casimir scalar.** `Ω` acts on `M(λ)` by the scalar `χ(λ) = ½ λ(λ+2)`.
2. **Degeneracy.** `χ(k) = χ(-k-2)` for every `k`. The vector `f^(k+1) v_k ∈ M(k)` is a highest-weight vector of
   weight `-k-2`, and it generates a submodule isomorphic to `M(-k-2)`, with `M(k)/M(-k-2) = L(k)`.
3. **No central separation.** Any element `z` of the centre `Z(U) = Q[Ω]` acts on `M(k)` and on its submodule
   `M(-k-2)` by the same scalar `p(χ(k))`. The same holds for any resolvent `(z - c)^(-1)` adjoined to make `z - c`
   invertible: it is defined on `M(k)` iff `c ≠ p(χ(k))`, and then defined on the whole of `M(k)`, submodule
   included. So no relation in the `Ω`-resolvent algebra annihilates the singular vector `f^(k+1) v_k` while
   keeping `L(k)`.

## Consequence

A finitely presented `sl_2`-type host cannot cut the Verma module `M(k)` down to `L(k)` by a Casimir relation, a
resolvent of the Casimir, or any central relation. The only element that does the cut is the singular vector
`f^(k+1) v_k`, whose expression has length growing with `k`. This is the growing-length relation again, now inside
the enveloping algebra.

A resolvent of `h` does not help either. `(h - c)^(-1)` is defined on a highest-weight module iff `c` is not a
weight; requiring it excludes the weight `c` in every module at once, so it cannot bound weights below by `-k`,
which depends on the top weight `k`.
