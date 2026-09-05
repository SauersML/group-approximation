---
rg: 2
id: all-representation-expansion-keeps-macroscopic-multiplicity-swap
kind: claim
title: Even expansion in every representation leaves a macroscopic spin-multiplicity swap
artifacts:
  - research/artifacts/unitary-expander-nonhyperlinearity-audit-2026-09-04.md
distinct_from:
  normalizer-multiplicity-twist-breaks-prefix-expander-rounding: that uses a rank-one invariant vector for a conjugate multiplicity twist; this gives a unitary invariant at distance tending to one and applies even to a gap uniform over every compact-group representation.
  quantum-expander-relative-commutant-rounding: that correctly fixes the checks as V_i tensor I; this proves that replacing them by diagonal V_i tensor V_i cannot yield its conclusion, even with an all-representation expander.
---

For every `d>=2`, let `F` be tensor flip on `C^d tensor C^d`, and let
`E=tr_d tensor id`, with its output embedded as `I_d tensor M_d`.
For every family `V_i in U(d)` one has

```text
[F,V_i tensor V_i]=0,
E(F)=I_(d^2)/d,
dist_2(F,I_d tensor M_d)^2=1-1/d^2.                   (UES1)
```

For every traceless unitary `a in M_d`,

```text
||[F,a tensor I_d]||_2^2=2.                           (UES2)
```

Consequently no dimension-independent commutant-rounding bound with error
tending to zero can turn commutation with the diagonal checks into
commutation with the old factor.  This remains false when the `V_i` have
a spectral gap uniform over all finite-dimensional continuous unitary
representations of `SU(d)`, and not just its adjoint representation.

The swap is itself in the invariant space of the amplified adjoint
representation.  An all-representation gap controls the complement of that
invariant space; it does not remove the invariant space.

For perturbed checks `D_i` with
`||D_i-V_i tensor V_i||_2<=epsilon`, the same fixed swap satisfies
`||[F,D_i]||_2<=2epsilon`, while the separation in `(UES1)` is unchanged.
Thus the obstruction also survives normalized-HS perturbation.

DERIVATION
all-representation-expander-swap-proof
