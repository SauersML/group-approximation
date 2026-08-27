---
rg: 2
id: canonical-moments-bound-projective-fixed-carrier-density
kind: claim
title: A finite canonical moment window sharply bounds every projective fixed carrier by its reciprocal length
distinct_from:
  unnamed-positive-density-fixed-space-is-terminal: that turns a supplied phase-one carrier of density greater than `1/N` into non-hyperlinearity; this gives the phase-uniform converse bound on every carrier compatible with the finite canonical moment window and proves sharpness at density `1/N`.
  finite-clock-fejer-threshold-is-sharp: that studies a named finite-order clock and its permitted return mass; this allows a model-dependent scalar phase and an arbitrary contraction carrier for any unitary with a canonical moment window.
  finite-swap-conjugate-moments-do-not-fold-arithmetic-double: that realizes arbitrary finite swap-word moment tables in finite quotients; this is the analytic inequality showing why those moments cannot manufacture a positive fold carrier.
---

**ESTABLISHED PHASE-UNIFORM FEJER FIREWALL.**  Let `V_n` be unitaries and
fix `N>=2`.  Suppose

```text
tr(V_n^k) -> 0                 (0<|k|<N).               (PFC1)
```

Let `lambda_n in T` be arbitrary phases and let `X_n` be arbitrary
contractions satisfying

```text
||(V_n-lambda_n)X_n||_2 ->0.                            (PFC2)
```

Then

```text
limsup_n ||X_n||_2^2 <= 1/N.                            (PFC3)
```

In particular, if `(PFC1)` holds for every fixed nonzero `k`, no projective
approximate fixed carrier can have any fixed positive density.  The phases
may vary adversarially with the matrix model; no subsequence or phase limit
is needed.

The constant is sharp for every finite window.  In the regular
`N`-dimensional representation of `C_N`, let `V` have all `N`-th roots of
unity once each and let `X` project onto any one eigenspace.  Then

```text
tr(V^k)=0       (0<|k|<N),
(V-lambda)X=0,
||X||_2^2=1/N.                                           (PFC4)
```

Thus a fixed canonical window cannot itself produce the carrier needed by a
positive-density return argument.  It is the terminal **upper test** which
contradicts a carrier supplied independently by arithmetic, geometry, or a
finite-coordinate decoder.

Applied to the fold word of the `SL_3` arithmetic double, canonical trace
moments alone therefore prove the negation of
`sl3-positive-density-projective-fold-sector` on every extant microstate
sequence.  Establishing that open sector assertion must mean proving, from
the arithmetic relations, that every hypothetical sequence also has the
forbidden carrier.  It cannot be inferred from its scalar canonical moments.
