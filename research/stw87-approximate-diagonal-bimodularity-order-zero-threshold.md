---
rg: 2
id: stw87-approximate-diagonal-bimodularity-order-zero-threshold
kind: claim
title: Diagonal order-zero recovery requires a macroscopic bimodularity defect
distinct_from:
  stw87-diagonal-bimodular-localization-no-go: that claim treats exactly diagonal-bimodular localizations and proves an exact factorization identity; this claim quantifies how far any diagonal-valued order-zero recovery must depart from fixing the diagonal or respecting singleton corners.
artifacts:
  - research/artifacts/stw87-diagonal-bimodular-localization-no-go-audit-2026-08-30.md
---

Let `X` be a countable discrete bounded-geometry metric space, set
`A=C*_u(X)` and `D=ell^infinity(X)`, and let `R:A->D` be c.p.c.  Define

```text
delta_D(R)=norm(R|_D-id_D),

delta_c(R)=sup {
  norm(p_x R(a) p_x-R(p_x a p_x)) :
  x in X, norm(a)<=1
}.
```

Then

```text
norm(R-E_X) <= delta_D(R)+delta_c(R).                  (A)
```

If `X` has at least two points and `phi:C^2->A` is the canonical Hadamard
two-point packet, order zero of `R phi` forces

```text
delta_D(R)+delta_c(R) >= 1/2.                          (B)
```

If `iota:M_n->A`, `n>=2`, is a canonical matrix-corner inclusion, order
zero of `R iota` forces

```text
delta_D(R)+delta_c(R) >= 1.                            (C)
```

Thus a diagonal-recovery map cannot both be approximately the identity on
the diagonal and approximately bimodular even just at all singleton corners
while retaining the order-zero packets of a nuclear-dimension approximation.
