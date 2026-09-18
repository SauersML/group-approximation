---
rg: 2
id: some-houghton-group-has-superquadratic-dehn-function
kind: claim
title: "Some Houghton group H_n (n >= 3) has Dehn function not bounded by a quadratic"
distinct_from:
  houghton-groups-have-quadratic-dehn-function: that is the assertion that every H_n is quadratic; this is its negation, that some H_n is not.
  some-houghton-group-has-superpolynomial-dehn-function: that asks for failure of every polynomial bound; this asks only for failure of the quadratic bound.
---

There is `n >= 3` such that `δ_(H_n)(x) ≼ x^2` fails.

## Attempts

- 2026-09-13 (z1-24-houghton): candidate families are words
  `[α, x α x^(-1)]` with `x` of length `L` moving `α` to a disjoint
  transposition, and nested products of far-apart transpositions whose
  commutation cannot be proved by transporting a bounded relator along a
  commuting path. `H_n` has no `BS(1,m)` with `|m| >= 2`, and finitary
  permutations are at most `P log P`-distorted (Burillo–Cleary–Martino–Röver,
  arXiv:1403.0026, Theorem 4.1). So an exponential mechanism is unlikely, but
  a polynomial gap such as `x^3` is not excluded. No lower bound beyond `x^2`
  is known.
- 2026-09-18 (swarm-0917-w13-w13-z-last1, cohomology-index): class kill,
  recorded as `houghton-cohomological-dehn-lower-bounds-cap-at-quadratic`
  (direct proof `houghton-cohomological-dehn-lower-bounds-cap-proof`).
  - Killed: every cocycle certificate whose module has `H^1(FSym; V) = 0`,
    which covers trivial and finite-dimensional coefficients. Also killed:
    every central-extension distortion bound and abelian-subgroup
    distortion. None of them gives more than `x^2`.
  - Where it dies: `H^2(FSym; V) = 0` always. Once `H^1` vanishes, inflation
    from `Z^(n-1)` is onto, so the certificate is a Euclidean area pairing
    plus a linear boundary term.
  - What survives: modules with `lim^1_i V^(Sym({1..n}x{1..i})) != 0`, for
    example `ℓ^∞(G)` (the LP dual of real filling). Non-abelian corridor or
    HNN arguments, counting on `FSym`, and asymptotic-cone arguments also
    survive.
  - Do not retry Gersten-style real 2-cocycles, finite-dimensional twisted
    cocycles or central-extension arguments.
