---
rg: 2
id: promislow-symmetric-piece-units-satisfy-gardam-equations
kind: claim
title: A unit of R[P] built from Gardam's symmetric pieces satisfies Gardam's equations up to a unit constant, so its inverse is Gardam's formula
distinct_from:
  murray-z-only-ansatz-has-no-char0-units: that excludes Murray's z-only shape in characteristic 0 and assumes the inverse is Gardam's formula; this holds over every domain for every element with symmetric pieces, and shows that formula is forced.
  unit-conjecture-fails-over-complex-numbers: that imports nontrivial complex units, and the imported unit does not have symmetric pieces; this is an exact unit criterion for elements that do.
  promislow-group-ring-units-are-constant-reduced-norm: that is the unit criterion for every element of R[P]; this evaluates it on the symmetric shape and derives Gardam's equations from it.
artifacts:
  - research/artifacts/promislow-reduced-norm-2026-09-13.md
---

**ESTABLISHED.** Notation as in `promislow-group-ring-units-are-constant-reduced-norm`.
Let `R` be a commutative domain, and let `p, q, r, s in R[L]`. Put

    p0 = x^(-1/2) y^(-1/2) p,   q0 = y^(1/2) q,   r0 = x^(-1/2) r,   s0 = s

in `R[x^(+-1/2), y^(+-1/2), z^(+-1)]`. Assume `p0, q0, r0, s0` are invariant
under `x -> x^-1, y -> y^-1` (the hypothesis of Gardam's Lemma 1,
arXiv:2102.11818). Let `f^A = f(x, y^-1, z^-1)` and define

    alpha  = p + q a + r b + s ab,
    alpha' = x^-1 p^A - x^-1 q a - y^-1 r b + z^-1 s^A ab,
    N  = p0 p0^A - q0 q0^A - r0 r0^A + s0 s0^A,
    xi = p0^A s0 - q0 r0^A,
    M  = x^(-1/2) y^(-1/2) (xi + z^-1 xi^A).

Here `N` and `M` lie in `R[L]`.

1. `alpha' alpha = N + M ab` and `alpha alpha' = N + x y M ab`.
2. `Nrd(alpha) = N^2 - x y z M^2`.
3. `alpha` is a unit of `R[P]` iff `M = 0` and `N in R^x`. In that case
   `alpha^-1 = N^-1 alpha'`.
4. The trivial units with symmetric pieces are exactly `lambda z^k ab` with
   `lambda in R^x` and `k in Z`.

Gardam's Lemma 1 is the "if" part of (3) with `N = 1`: his equations (1) and
(2) say `M = 0` and `N = 1`. By (3) the lemma is exact up to a unit constant.
No unit with symmetric pieces has an inverse of any other shape, and on this
shape the unit problem over `R` is exactly the system `M = 0`, `N in R^x`.

**Instances.** Gardam's unit of `F_2[P]` (Theorem A) has symmetric pieces, and
so do Murray's units of `F_d[P]` for odd primes `d` (their shape, recorded in
`murray-z-only-ansatz-has-no-char0-units`, has symmetric pieces; see
`murray-z-only-shape-has-no-char0-units-any-inverse`). Gardam's complex unit
(arXiv:2312.05240) does not. Its coset-1 coefficient is
`1 + t^2 x z^-1 - t^2 x^-1 z^-1 - s^2 y z^-1 + s^2 y^-1 z^-1`. So
`p0 = x^(-1/2) y^(-1/2) p` contains `x^(-1/2) y^(-1/2)` but not
`x^(1/2) y^(1/2)`, and is not invariant.

**Scope.** This proves no triviality. Whether `M = 0, N in K^x` has a
nontrivial solution over a field of characteristic 0 is open for symmetric
pieces of arbitrary shape. It is excluded for Murray's z-only shape by
`murray-z-only-shape-has-no-char0-units-any-inverse`.

DERIVATION
[[promislow-symmetric-piece-units-proof]]
