---
rg: 2
id: normal-fibre-galois-games-round-linearly-over-all-groups
kind: claim
title: For normal K over every finite G of exponent m, SDP 1-eps gives L meeting K trivially with mu(G minus L) <= 3 eps log_q k / min(1-cos(2pi/m), 1-gamma(G))
distinct_from:
  normal-fibre-galois-games-round-linearly-over-m-groups: that is the monomial case with constant 1 - cos(2 pi/m); this removes the monomial hypothesis through primitive inducing representations and the trace gap.
  galois-games-round-through-free-subgroups: that pays the dimensions of the irreducibles carrying the certificate; this pays only a trace-gap constant.
artifacts:
  - research/artifacts/ugc-rounding-normal-fibres-2026-09-13.md
  - research/artifacts/ugc-rounding-normal-fibres-part2-2026-09-13.md
---

**ESTABLISHED.** Notation of `galois-unique-game-value-is-transversal-expansion`.
Let `G` be finite of exponent `m`, `K` normal of order `k`, `q` the least prime
dividing `k`, and `mu` symmetric and conjugation-invariant. Suppose some
admissible certificate has `sum mu phi >= 1 - eps`, for instance
`SDP Gal(G,K,mu) >= 1 - eps`. Put
`c(G,m) = min(1 - cos(2 pi/m), 1 - gamma(G))`, with `gamma(G)` from
`primitive-projective-representations-have-a-trace-gap`. Then some `L <= G`,
an intersection of at most `log_q k` conjugates of kernels of primitive
representations of subgroups, has `L cap K = {e}` and

```text
mu(G \ L) <= 3 eps log_q k / c(G,m),     so     val Gal(G,K,mu) >= 1 - 3 eps log_q k / c(G,m).
```

* **Solvable `G`.** `c = min(1 - cos(2 pi/m), 1 - 2^(-1/2))`, which depends only on
  `m` and equals `1 - cos(2 pi/m)` for `m >= 8`. So the normal-`K` form of
  `free-subgroup-rounding-is-universal-at-bounded-exponent` holds over solvable
  groups with the abelian constant.
* **All finite groups, uniformly in `m`.** Only finitely many nonabelian simple
  groups have exponent dividing `m` [CFSG, recalled], so
  `sup { gamma(G) : exp G | m } < 1`. This uniformity rests on the
  classification; the displayed bound for each `G` does not.
* **Mechanism.** `rho = Ind_H sigma` with `sigma` primitive. Against
  conjugation-invariant `mu`, `lambda_rho = sum_(h in H) mu(h) chi_sigma(h)/d_sigma`.
  On `H \ ker sigma` the summand's deficit is at least `1 - cos(2 pi/m)` for
  scalars and at least `1 - gamma(G)` otherwise. So
  `mu(G \ ker sigma) <= (1 - lambda_rho)/c`. Then a halving chain inside `K` runs
  through conjugates of the primitive kernels.
* **Tight shape.** Khot--Vishnoi forces `log k`, and the odd cycle `Z_(2n)`
  forces dependence on `m`. For non-normal `K` the free form fails
  (`free-subgroup-rounding-fails-for-non-normal-fibres`), and the extra factor
  `[G : N_G(K)]` is necessary and sufficient
  (`free-rounding-pays-the-number-of-fibre-conjugates`).

For rounding, this means that symmetric quotient instances with normal fibres
over bounded-exponent groups separate SDP from value only when
`eps log k -> infinity`, as over `F_2^N`: non-abelian symmetry of bounded exponent
adds no integrality gap. It neither proves nor refutes `unique-games-conjecture`.
