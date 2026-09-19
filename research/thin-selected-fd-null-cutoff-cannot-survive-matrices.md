---
rg: 2
id: thin-selected-fd-null-cutoff-cannot-survive-matrices
kind: claim
title: The universal thin finite-dimensional-null cutoff cannot survive on a selected matrix-origin unitary
distinct_from:
  thin-selected-module-is-profinite-continuous: that demands weak containment, hence every finite-dimensional-norm inequality, on the whole selected cyclic module; this asks for one fixed exponentially null sequence and one vector only.
  thin-sln-robust-relative-commutant-transfer: that is stated as a dimension-free commutator modulus; this is the exact C-star-algebraic upper-semicontinuity statement which would produce that modulus by compactness.
---

Let `(y_N)` be the explicit sequence in
`thin-leak-has-universal-fd-null-laplacian-witness`.  Suppose `U_k` is any
normalized-Hilbert--Schmidt asymptotic matrix representation of a fixed
presentation of `A=SL_3(Z)`, inducing

```text
pi:A->U(M_omega),   alpha=Ad pi,
```

and suppose `v in U(M_omega)` centralizes the displayed thin subgroup
`C=<a,b>`.  Assert the single-sequence upper-semicontinuity

```text
lim_(N->infinity) ||alpha(y_N)v||_2=0.                 (SFC1)
```

This is strictly weaker than finite-dimensional-norm continuity of the
whole cyclic module: only the universal positive-gap cutoff `(y_N)` is
tested.  Since `||y_N||_FD<=2q^N`, `(SFC1)` says precisely that matrix origin
does not permit this one finite-dimensional-null sequence to retain mass on
the selected unitary.

## Equivalent finite inequality

For every `epsilon>0`, `(SFC1)` is equivalent by ultraproduct compactness to
the existence of `N` and `delta>0` such that any finite matrix tuple with
presentation defect below `delta`, together with a unitary `v` whose
`a,b`-commutators are below `delta`, satisfies

```text
|| y_N(Ad U) v ||_2 < epsilon.                          (SFC2)
```

Here `N` is chosen first, so `(SFC2)` is a genuinely finite word test.  The
unknown content is an upper-semicontinuity modulus comparing this fixed
almost-representation evaluation with its finite-dimensional representation
norm; ordinary relator telescoping gives no such comparison.

## Attempts

- Full selected profinite continuity implies `(SFC1)`, but controls every
  group-ring element and is stronger than necessary.
- Exact finite-dimensional representations satisfy `(SFC2)` with
  `delta=0` by `(ULW2)`.  Extending this to small normalized-HS relator defect
  is the unresolved robustification; the support length of `y_N` grows with
  `N`, so a diagonal telescoping argument has no uniform modulus.
- The canonical thin HNN model has
  `||alpha(y_N)v||_2=||[v,pi(r)]-1||_2>0` for every `N`.
  Hence group relations, positivity, and the canonical character alone do
  not prove `(SFC1)`; matrix origin must be used.
- A sofic atlas for `A curvearrowright A/C` embeds that canonical model in a
  matrix ultraproduct and refutes `(SFC1)`.  Thus permutation rounding again
  reaches the nonnormal stability-in-finite-actions wall.
- Tensor amplification does give one genuine matrix-origin reduction:
  `thin-selected-leak-amplifies-to-codense-quasiregular-profile` turns any
  leak into the exact coefficient `1_H` of `lambda_(A/H)` for a proper
  profinitely dense `H` containing `C`.  What it does not provide is the
  permutation atlas needed to invoke finite-action stability.

**Status: OPEN.**
