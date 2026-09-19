---
rg: 2
id: fixed-summable-kazhdan-residual-square-functions-vanish
kind: claim
title: Fixed summable residual ledgers vanish pointwise and cannot be supplied by tracial Kazhdan expansion
distinct_from:
  kt-kazhdan-edge-grams-are-conditioned-only-at-fixed-radius: That shows moving edge-word Grams can be arbitrarily ill-conditioned; this proves that even perfect conditioning cannot make a fixed summable weighted list of pointwise-vanishing residuals charge a return.
  kt-infinite-index-returns-force-divergent-edge-leakage: That shows the necessary leakage is detected by an unbounded moving family of exterior returns; this proves why a fixed probability-weighted residual family cannot replace that moving family.
  exterior-return-loss-has-quarter-trace-support: That supplies a fixed positive-trace physical support from the return expectation itself; this rules out controlling that support by a fixed summable ledger of ordinary actor defects.
---

Let `e_(j,n)` be any countable family of normalized-Hilbert--Schmidt actor
residuals such that

```text
0<=e_(j,n)<=2,
e_(j,n)->0 for every fixed j.                          (KSV1)
```

For every fixed summable nonnegative weight sequence `(a_j)`,

```text
sum_j a_j e_(j,n)^2 ->0.                               (KSV2)
```

This remains true if the residuals are organized along the Schreier graph
`Gamma/(t Gamma t^(-1))` and the weights are a fixed probability measure, a
fixed heat-kernel/Kazhdan average, or any other fixed `ell^1` weighting.

Consequently an inequality of the form

```text
1-||E_(B_n)(phi_n(h))||_2^2
 <= C sum_j a_j e_(j,n)^2                              (KSV3)
```

would rule out every relative microstate sequence with one vanished exterior
return: the left side would tend to one, whereas `(KSV2)` makes the right side
tend to zero.  Thus proving `(KSV3)` would be a genuinely finite-matrix
obstruction, not a routine summation of the actor defects.

In fact `(KSV3)` is false in the exact regular tracial model.  In `L(G)`, put

```text
B=L(Gamma),       T=lambda(t),
h=t^(-1)gamma t outside Gamma.                         (KSV4)
```

Then every actor multiplication residual is zero while

```text
E_B(lambda(h))=0.                                      (KSV5)
```

The quasi-regular representation on
`ell^2(Gamma/(t Gamma t^(-1)))` has the Kazhdan/Schreier spectral gap because
the index is infinite and `Gamma` has property `(T)`.  Hence that spectral gap
coexists exactly with `(KSV4)--(KSV5)`; it propagates the exterior-return
vector into a legitimate infinite quasi-regular module rather than charging
an actor relation defect.

Therefore property `(T)` and Schreier expansion **alone**, through arguments
valid in arbitrary finite tracial von Neumann algebras, cannot prove `(KSV3)`.
A finite-dimensional version is not disproved, but it would have to use a
matrix-only ingredient absent from the regular model--for example rank
integrality, finite-dimensional no-growth, or an authenticated common carrier.

Therefore a successful square-function upgrade must use at least one
of the following genuinely extra ingredients:

1. a model-dependent moving radius or nonsummable family, as already forced
   by `kt-infinite-index-returns-force-divergent-edge-leakage`;
2. a single fixed group-algebra checksum encoding infinitely many scales; or
3. an authentication theorem turning the quarter-trace support from
   `exterior-return-loss-has-quarter-trace-support` into a common reducing
   actor carrier.

DERIVATION
fixed-summable-residual-dominated-convergence-proof
