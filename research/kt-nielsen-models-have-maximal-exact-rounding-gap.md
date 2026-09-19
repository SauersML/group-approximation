---
rg: 2
id: kt-nielsen-models-have-maximal-exact-rounding-gap
kind: claim
title: Strong Kun--Thom Nielsen models are maximally far from every exact equivariant model
distinct_from:
  finite-dimensional-nielsen-cocycle-models-kill-mark: that says an exact finite-dimensional equivariant model kills the marked free generator; this compares every strong approximate model with every exact model and computes the sharp operator-norm rounding distance two.
  sofic-nielsen-charts-defeat-uniform-compact-collapse: that constructs approximate Hilbert--Schmidt charts for a different sofic compressor pair and obtains square-root-two separation; this is an operator-norm statement for any strong model of the actual Kun--Thom pair.
artifacts:
  - research/artifacts/kt-double-mf-trace-literature-audit-2026-08-30.md
---

Fix the Kun--Thom marked element `h in <<Gamma>>_G` with `h o!=o` used in
`finite-dimensional-nielsen-cocycle-models-kill-mark`, and put

```text
x_*=h o,                     b_*=b_(x_*).                (NMG1)
```

Let `(U_n,V_n)` be **any** sequence satisfying `(SNM1)--(SNM5)` of
`kt-strong-nielsen-covariant-microstates`; existence is not assumed.  For
each `n`, let

```text
beta_n:G->Aut(M_(d_n)),       theta_n:N->U(d_n)           (NMG2)
```

be any exact action and exact equivariant homomorphism:

```text
theta_n(alpha_g(a))=beta_(n,g)(theta_n(a)).               (NMG3)
```

Then

```text
||V_n(x_*)-theta_n(b_*)|| ->2.                            (NMG4)
```

The constant `2` is maximal for two unitaries.  In particular, no strong
Nielsen package can be perturbed, amplified, or conjugated by `o(1)` in
operator norm into exact finite-dimensional equivariant models, even on the
single fixed radical generator `b_*`.

DERIVATION
kt-nielsen-maximal-rounding-gap-proof
